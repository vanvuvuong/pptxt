// pptxt v2 - ship a .pptx (or any file) through a chat as text, smallest possible, verified.
//
// Pipeline (enc): unzip .pptx -> pack all parts into one stream -> Brotli q11 (solid)
//
//	-> Base32768 (default), Z85 or Base64 -> split into parts <= char limit.
//
// Guarantee: content-identical. Every part name, part order and part byte is identical
// to the original (so every slide, XML part and image pixel is identical). Only the
// outer zip container bytes may differ. Files that are not zip are shipped byte-identical.
//
// Verification: each text part carries its own checksum (finds the corrupted part),
// the whole content carries a SHA-256. enc self-tests the full round trip before writing;
// dec rebuilds, re-reads the rebuilt file, and only then writes it.
package main

import (
	"archive/zip"
	"bytes"
	"compress/flate"
	"crypto/sha256"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode/utf16"
	"unicode/utf8"

	"github.com/Max-Sum/base32768"
	"github.com/andybalholm/brotli"
)

const magic = "PPTXT2 "
const headerReserve = 220 // chars reserved per part for the header line

func die(f string, a ...any) {
	fmt.Fprintf(os.Stderr, "ERROR: "+f+"\n", a...)
	os.Exit(1)
}

func usage() {
	fmt.Fprintln(os.Stderr, `pptxt v2 - ship a .pptx through chat as text (smallest, verified)

  pptxt enc [-e b32k|z85|b64] [-limit 40000] <input.pptx> <output.txt>
      -e b32k   Base32768 (default, most compact): ~2.5x denser than base64, Unicode
      -e z85    Z85: ASCII, ~6% denser than base64, paste inside a code block
      -e b64    Base64: ASCII, most compatible
      -limit    max characters per line = per message (default 40000)
      -split    write one file per part (output.001.txt ...) instead of one line per part
      -> default: output.txt, one part per line; send each line as one message

  pptxt dec <output.pptx> <part.txt> [more parts ...]
      paste received messages into one file (one per line) or several files, any order`)
	os.Exit(2)
}

func main() {
	if len(os.Args) < 2 {
		usage()
	}
	switch os.Args[1] {
	case "enc":
		fs := flag.NewFlagSet("enc", flag.ExitOnError)
		fs.Usage = usage
		e := fs.String("e", "b32k", "")
		limit := fs.Int("limit", 40000, "")
		split := fs.Bool("split", false, "")
		fs.Parse(os.Args[2:])
		if fs.NArg() != 2 || (*e != "b32k" && *e != "z85" && *e != "b64") || *limit < headerReserve+100 {
			usage()
		}
		cmdEnc(fs.Arg(0), fs.Arg(1), *e, *limit, *split)
	case "dec":
		if len(os.Args) < 4 {
			usage()
		}
		cmdDec(os.Args[2], os.Args[3:])
	default:
		usage()
	}
}

// ---------- payload: kind 'Z' (zip parts) or 'R' (raw bytes) ----------

type entry struct {
	name     string
	method   uint16
	modified int64
	data     []byte
}

type content struct {
	isZip   bool
	comment string
	entries []entry
	raw     []byte
}

func readContent(path string) (*content, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	zr, err := zip.NewReader(bytes.NewReader(data), int64(len(data)))
	if err != nil { // not a zip: ship raw, byte-identical
		return &content{raw: data}, nil
	}
	c := &content{isZip: true, comment: zr.Comment}
	for _, f := range zr.File {
		rc, err := f.Open()
		if err != nil {
			return nil, fmt.Errorf("%s: %v", f.Name, err)
		}
		d, err := io.ReadAll(rc)
		rc.Close()
		if err != nil {
			return nil, fmt.Errorf("%s: %v", f.Name, err)
		}
		c.entries = append(c.entries, entry{f.Name, f.Method, f.Modified.Unix(), d})
	}
	return c, nil
}

// contentHash: order + names + bytes of every part (zip), or the raw bytes.
func (c *content) hash() string {
	h := sha256.New()
	if !c.isZip {
		h.Write([]byte("R"))
		h.Write(c.raw)
	} else {
		h.Write([]byte("Z"))
		for _, e := range c.entries {
			s := sha256.Sum256(e.data)
			h.Write([]byte(e.name))
			h.Write([]byte{0})
			h.Write(s[:])
		}
	}
	return hex.EncodeToString(h.Sum(nil))
}

func (c *content) originalSize() int {
	if !c.isZip {
		return len(c.raw)
	}
	n := 0
	for _, e := range c.entries {
		n += len(e.data)
	}
	return n
}

func putBytes(b *bytes.Buffer, d []byte) {
	var t [binary.MaxVarintLen64]byte
	b.Write(t[:binary.PutUvarint(t[:], uint64(len(d)))])
	b.Write(d)
}

func (c *content) marshal() []byte {
	var b bytes.Buffer
	var t [binary.MaxVarintLen64]byte
	if !c.isZip {
		b.WriteByte('R')
		putBytes(&b, c.raw)
		return b.Bytes()
	}
	b.WriteByte('Z')
	putBytes(&b, []byte(c.comment))
	b.Write(t[:binary.PutUvarint(t[:], uint64(len(c.entries)))])
	for _, e := range c.entries {
		putBytes(&b, []byte(e.name))
		b.Write(t[:binary.PutUvarint(t[:], uint64(e.method))])
		b.Write(t[:binary.PutVarint(t[:], e.modified)])
	}
	// names/metadata first, then all data: groups similar bytes for better compression
	for _, e := range c.entries {
		putBytes(&b, e.data)
	}
	return b.Bytes()
}

type reader struct{ *bytes.Reader }

func (r reader) uv() uint64 {
	v, err := binary.ReadUvarint(r)
	if err != nil {
		panic(err)
	}
	return v
}
func (r reader) bytes() []byte {
	n := r.uv()
	if n > uint64(r.Len()) {
		panic(errors.New("length out of range"))
	}
	d := make([]byte, n)
	io.ReadFull(r, d)
	return d
}

func unmarshal(p []byte) (c *content, err error) {
	defer func() {
		if r := recover(); r != nil {
			c, err = nil, fmt.Errorf("payload is malformed: %v", r)
		}
	}()
	r := reader{bytes.NewReader(p)}
	k, _ := r.ReadByte()
	switch k {
	case 'R':
		return &content{raw: r.bytes()}, nil
	case 'Z':
		c = &content{isZip: true, comment: string(r.bytes())}
		n := r.uv()
		if n > uint64(len(p)) {
			panic(errors.New("entry count out of range"))
		}
		c.entries = make([]entry, n)
		for i := range c.entries {
			c.entries[i].name = string(r.bytes())
			c.entries[i].method = uint16(r.uv())
			m, err := binary.ReadVarint(r)
			if err != nil {
				panic(err)
			}
			c.entries[i].modified = m
		}
		for i := range c.entries {
			c.entries[i].data = r.bytes()
		}
		return c, nil
	}
	return nil, errors.New("unknown payload kind")
}

func (c *content) build() ([]byte, error) {
	if !c.isZip {
		return c.raw, nil
	}
	var b bytes.Buffer
	w := zip.NewWriter(&b)
	w.RegisterCompressor(zip.Deflate, func(out io.Writer) (io.WriteCloser, error) {
		return flate.NewWriter(out, flate.BestCompression)
	})
	for _, e := range c.entries {
		m := e.method
		if m != zip.Store {
			m = zip.Deflate
		}
		fw, err := w.CreateHeader(&zip.FileHeader{Name: e.name, Method: m, Modified: time.Unix(e.modified, 0)})
		if err != nil {
			return nil, err
		}
		if _, err := fw.Write(e.data); err != nil {
			return nil, err
		}
	}
	if c.comment != "" {
		w.SetComment(c.comment)
	}
	if err := w.Close(); err != nil {
		return nil, err
	}
	return b.Bytes(), nil
}

// ---------- compression ----------

func compress(d []byte) []byte {
	var b bytes.Buffer
	w := brotli.NewWriterOptions(&b, brotli.WriterOptions{Quality: 11, LGWin: 24})
	w.Write(d)
	w.Close()
	return b.Bytes()
}

func decompress(d []byte) ([]byte, error) {
	return io.ReadAll(brotli.NewReader(bytes.NewReader(d)))
}

// ---------- text encodings ----------

const z85chars = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ.-:+=^!/*?&<>()[]{}@%$#"

func z85enc(d []byte) (string, int) {
	pad := (4 - len(d)%4) % 4
	d = append(append([]byte{}, d...), make([]byte, pad)...)
	out := make([]byte, 0, len(d)/4*5)
	for i := 0; i < len(d); i += 4 {
		v := binary.BigEndian.Uint32(d[i:])
		var t [5]byte
		for j := 4; j >= 0; j-- {
			t[j] = z85chars[v%85]
			v /= 85
		}
		out = append(out, t[:]...)
	}
	return string(out), pad
}

func z85dec(s string, pad int) ([]byte, error) {
	var idx [256]int
	for i := range idx {
		idx[i] = -1
	}
	for i := 0; i < len(z85chars); i++ {
		idx[z85chars[i]] = i
	}
	if len(s)%5 != 0 || pad < 0 || pad > 3 {
		return nil, errors.New("bad Z85 length")
	}
	out := make([]byte, 0, len(s)/5*4)
	for i := 0; i < len(s); i += 5 {
		var v uint64
		for j := 0; j < 5; j++ {
			c := idx[s[i+j]]
			if c < 0 {
				return nil, fmt.Errorf("invalid character %q", s[i+j])
			}
			v = v*85 + uint64(c)
		}
		if v > 0xFFFFFFFF {
			return nil, errors.New("invalid Z85 block")
		}
		var t [4]byte
		binary.BigEndian.PutUint32(t[:], uint32(v))
		out = append(out, t[:]...)
	}
	if pad > len(out) {
		return nil, errors.New("bad padding")
	}
	return out[:len(out)-pad], nil
}

// ---------- parts ----------

type part struct {
	enc         string
	idx, total  int
	length, pad int
	psum, chash string
	body        string
}

func psum(s string) string {
	h := sha256.Sum256([]byte(s))
	return hex.EncodeToString(h[:8])
}

func makeParts(text []rune, enc string, pad int, chash string, limit int) []string {
	per := limit - headerReserve
	n := (len(text) + per - 1) / per
	if n == 0 {
		n = 1
	}
	out := make([]string, n)
	for i := 0; i < n; i++ {
		a, b := i*per, (i+1)*per
		if b > len(text) {
			b = len(text)
		}
		body := string(text[a:b])
		out[i] = fmt.Sprintf("%senc=%s part=%d/%d len=%d pad=%d psum=%s content=%s %s",
			magic, enc, i+1, n, b-a, pad, psum(body), chash, body)
	}
	return out
}

func decodeUTF16(b []byte, be bool) string {
	u := make([]uint16, len(b)/2)
	for i := range u {
		if be {
			u[i] = uint16(b[2*i])<<8 | uint16(b[2*i+1])
		} else {
			u[i] = uint16(b[2*i+1])<<8 | uint16(b[2*i])
		}
	}
	return string(utf16.Decode(u))
}

func normalize(raw []byte) string {
	var s string
	switch {
	case len(raw) >= 2 && raw[0] == 0xFF && raw[1] == 0xFE:
		s = decodeUTF16(raw[2:], false)
	case len(raw) >= 2 && raw[0] == 0xFE && raw[1] == 0xFF:
		s = decodeUTF16(raw[2:], true)
	default:
		s = strings.TrimPrefix(string(raw), "\uFEFF")
	}
	return strings.ReplaceAll(s, "\r", "")
}

func parseParts(texts map[string]string) ([]part, error) {
	byIdx := map[int]part{}
	var ref *part
	for src, t := range texts {
		segs := strings.Split(t, magic)
		if len(segs) < 2 {
			return nil, fmt.Errorf("%s: no PPTXT2 header found", src)
		}
		for _, seg := range segs[1:] {
			ci := strings.Index(seg, "content=")
			if ci < 0 || len(seg) < ci+8+64 {
				return nil, fmt.Errorf("%s: bad header near %q", src, firstN(seg, 80))
			}
			header, body := seg[:ci+8+64], seg[ci+8+64:]
			kv := map[string]string{}
			for _, f := range strings.Fields(header) {
				k, v, _ := strings.Cut(f, "=")
				kv[k] = v
			}
			var p part
			var err1, err2, err3, err4 error
			p.enc, p.psum, p.chash = kv["enc"], kv["psum"], kv["content"]
			ps := strings.SplitN(kv["part"], "/", 2)
			if len(ps) != 2 {
				return nil, fmt.Errorf("%s: bad header %q", src, header)
			}
			p.idx, err1 = strconv.Atoi(ps[0])
			p.total, err2 = strconv.Atoi(ps[1])
			p.length, err3 = strconv.Atoi(kv["len"])
			p.pad, err4 = strconv.Atoi(kv["pad"])
			if err1 != nil || err2 != nil || err3 != nil || err4 != nil || p.chash == "" || p.psum == "" {
				return nil, fmt.Errorf("%s: bad header %q", src, header)
			}
			// drop whitespace and backticks (code-block fences); neither is in either alphabet
			body = strings.Map(func(r rune) rune {
				if r == '`' || r == ' ' || r == '\n' || r == '\t' || r == '\u00a0' {
					return -1
				}
				return r
			}, body)
			got := utf8.RuneCountInString(body)
			if got < p.length {
				return nil, fmt.Errorf("part %d/%d is truncated: has %d of %d characters - copy it again", p.idx, p.total, got, p.length)
			}
			if got > p.length {
				return nil, fmt.Errorf("part %d/%d has %d extra characters after it - remove any text you added", p.idx, p.total, got-p.length)
			}
			p.body = body
			if psum(body) != p.psum {
				return nil, fmt.Errorf("part %d/%d is corrupted (checksum mismatch) - copy it again", p.idx, p.total)
			}
			if ref == nil {
				r := p
				ref = &r
			} else if p.total != ref.total || p.chash != ref.chash || p.enc != ref.enc || p.pad != ref.pad {
				return nil, fmt.Errorf("part %d belongs to a different file", p.idx)
			}
			if p.idx < 1 || p.idx > p.total {
				return nil, fmt.Errorf("invalid part number %d/%d", p.idx, p.total)
			}
			if _, dup := byIdx[p.idx]; dup {
				return nil, fmt.Errorf("part %d given twice", p.idx)
			}
			byIdx[p.idx] = p
		}
	}
	var miss []string
	out := []part{}
	for i := 1; i <= ref.total; i++ {
		p, ok := byIdx[i]
		if !ok {
			miss = append(miss, strconv.Itoa(i))
			continue
		}
		out = append(out, p)
	}
	if len(miss) > 0 {
		return nil, fmt.Errorf("missing part(s) %s of %d", strings.Join(miss, ", "), ref.total)
	}
	sort.Slice(out, func(a, b int) bool { return out[a].idx < out[b].idx })
	return out, nil
}

// fullDecode: text parts -> rebuilt file bytes, verified.
func fullDecode(texts map[string]string) ([]byte, *content, error) {
	parts, err := parseParts(texts)
	if err != nil {
		return nil, nil, err
	}
	var sb strings.Builder
	for _, p := range parts {
		sb.WriteString(p.body)
	}
	var blob []byte
	switch parts[0].enc {
	case "b32k":
		blob, err = base32768.SafeEncoding.DecodeString(sb.String())
	case "z85":
		blob, err = z85dec(sb.String(), parts[0].pad)
	case "b64":
		blob, err = base64.StdEncoding.DecodeString(sb.String())
	default:
		err = fmt.Errorf("unknown encoding %q", parts[0].enc)
	}
	if err != nil {
		return nil, nil, fmt.Errorf("decode failed: %v", err)
	}
	payload, err := decompress(blob)
	if err != nil {
		return nil, nil, fmt.Errorf("decompress failed: %v", err)
	}
	c, err := unmarshal(payload)
	if err != nil {
		return nil, nil, err
	}
	if c.hash() != parts[0].chash {
		return nil, nil, errors.New("content hash mismatch after decoding")
	}
	file, err := c.build()
	if err != nil {
		return nil, nil, err
	}
	// re-read what we built, independently, and check it again
	tmp := filepath.Join(os.TempDir(), fmt.Sprintf("pptxt-verify-%d", time.Now().UnixNano()))
	if err := os.WriteFile(tmp, file, 0600); err != nil {
		return nil, nil, err
	}
	defer os.Remove(tmp)
	re, err := readContent(tmp)
	if err != nil {
		return nil, nil, err
	}
	if re.isZip != c.isZip || re.hash() != parts[0].chash {
		return nil, nil, errors.New("rebuilt file does not match the original content")
	}
	return file, c, nil
}

// ---------- commands ----------

func cmdEnc(in, out, enc string, limit int, split bool) {
	st, err := os.Stat(in)
	if err != nil {
		die("%v", err)
	}
	c, err := readContent(in)
	if err != nil {
		die("%v", err)
	}
	chash := c.hash()
	blob := compress(c.marshal())
	var text string
	pad := 0
	switch enc {
	case "b32k":
		text = base32768.SafeEncoding.EncodeToString(blob)
	case "z85":
		text, pad = z85enc(blob)
	case "b64":
		text = base64.StdEncoding.EncodeToString(blob)
	}
	parts := makeParts([]rune(text), enc, pad, chash, limit)

	// self-test: full round trip in memory before writing anything
	texts := map[string]string{}
	for i, p := range parts {
		texts[strconv.Itoa(i)] = p
	}
	if _, _, err := fullDecode(texts); err != nil {
		die("self-test failed, nothing written: %v", err)
	}
	for i, p := range parts {
		if n := utf8.RuneCountInString(p); n > limit {
			die("internal: part %d is %d chars > limit %d", i+1, n, limit)
		}
	}

	maxChars := 0
	for _, p := range parts {
		if n := utf8.RuneCountInString(p); n > maxChars {
			maxChars = n
		}
	}
	if split {
		ext := filepath.Ext(out)
		base := strings.TrimSuffix(out, ext)
		for i, p := range parts {
			name := out
			if len(parts) > 1 {
				name = fmt.Sprintf("%s.%03d%s", base, i+1, ext)
			}
			if err := os.WriteFile(name, []byte(p+"\n"), 0644); err != nil {
				die("%v", err)
			}
			fmt.Printf("wrote %s (%d chars)\n", name, utf8.RuneCountInString(p))
		}
	} else {
		if err := os.WriteFile(out, []byte(strings.Join(parts, "\n")+"\n"), 0644); err != nil {
			die("%v", err)
		}
		fmt.Printf("wrote %s: %d line(s), longest %d chars - send each line as one message\n", out, len(parts), maxChars)
	}
	mode := "raw file (byte-identical)"
	if c.isZip {
		mode = fmt.Sprintf("zip, %d parts (content-identical)", len(c.entries))
	}
	b64 := (st.Size() + 2) / 3 * 4
	fmt.Printf("OK  self-test passed\n    mode:  %s\n    input: %d bytes, compressed: %d bytes\n    text:  %d chars in %d message(s)  (plain base64 would be %d chars, %.0f%% less)\n    content sha256=%s\n",
		mode, st.Size(), len(blob), utf8.RuneCountInString(text), len(parts), b64,
		100*(1-float64(utf8.RuneCountInString(text))/float64(b64)), chash)
}

func cmdDec(out string, files []string) {
	texts := map[string]string{}
	for _, f := range files {
		raw, err := os.ReadFile(f)
		if err != nil {
			die("%v", err)
		}
		texts[f] = normalize(raw)
	}
	file, c, err := fullDecode(texts)
	if err != nil {
		die("%v - nothing written", err)
	}
	if err := os.WriteFile(out, file, 0644); err != nil {
		die("%v", err)
	}
	what := "byte-identical"
	if c.isZip {
		what = fmt.Sprintf("%d parts content-identical", len(c.entries))
	}
	fmt.Printf("OK  wrote %s (%d bytes), verified: %s\n    content sha256=%s\n", out, len(file), what, c.hash())
}

func firstN(s string, n int) string {
	r := []rune(s)
	if len(r) > n {
		r = r[:n]
	}
	return string(r)
}
