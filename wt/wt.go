package main 

import (
	"fmt"
	"math/rand"
	"math"
	"os"
	"bufio"
	"encoding/gob"
	"encoding/json"
	"sort"
	"strings"
	"strconv"
	"bytes"
	"time"
	"github.com/bradleyjkemp/memviz"
)

// bitvec structure
type bitvec struct {
	bits []uint8
}

// create a bit vector
func makeBitvec(input []bool) *bitvec {
	size := (len(input) / 8)

	if len(input) % 8 > 0 {
		size += 1
	}

	// fmt.Println("size ", size)
	bvec := new(bitvec)
	bvec.bits = make([]uint8, size)

	val := 0

	if input[0] == true {
		val += int(math.Pow(float64(2), float64(7)))
	}
	// fmt.Println("val ", val)
	// fmt.Println("len(input) ", len(input))

	for i := 1; i < len(input); i++ {

		// fmt.Println("i ", i)

		if i/8 == 0 {
			// fmt.Println("i/8 == 0 ", i/8)

			bvec.bits[i/8] = uint8(val)
			val = 0
		}

		mod := 7 - (i % 8)

		// fmt.Println("mod ", mod)

		if input[i] == true {
			val += int(math.Pow(float64(2), float64(mod)))
		}
	}

	return bvec
}

// use bitwise AND to get bit at a position
func (bv bitvec) getBitAt(i int) uint8 {
	block := i / 8
	mod := i % 8

	bitcheck := uint8(math.Pow(float64(2), float64(mod)))

	if bv.bits[block] & bitcheck == 0 {
		return 0
	}
	
	return 1
}

// rank-select structure
type rs_struct struct {
	Bits *bitvec
	Sblocks []int
	Sblock_length int
	Blocks []int
	Block_slice []int
	Block_length int
	Table map[int][]int
}

func build_rank_select(bits []bool) *rs_struct {
	l := float64(len(bits))
	sblock_size := int(math.Pow(math.Log2(l), 2)/2)
	block_size := int(math.Log2(l)/2)

	rs := new(rs_struct)
	rs.Bits = makeBitvec(bits)
	rs.Sblocks = make([]int, int(math.Ceil(l/float64(sblock_size))))
	rs.Sblock_length = sblock_size
	rs.Blocks = make([]int, int(math.Ceil(l/float64(block_size))))
	rs.Block_slice = make([]int, int(math.Ceil(l/float64(block_size))))
	rs.Block_length = block_size
	rs.Table = make(map[int][]int)

	global_rank := 0
	last_block_rank := 0

	if bits[0] == true {
		global_rank++
	}
	rs.Sblocks[0] = 0
	rs.Blocks[0] = 0
	temp_block_val := 0

	if bits[0] == true {
		temp_block_val = int(math.Pow(2, float64(block_size - 1)))
	}

	for i := 1; i < len(bits); i++ {
		// fmt.Println(i, (i%block_size))
		if i % sblock_size == 0 {
			last_block_rank = global_rank
			rs.Sblocks[i/sblock_size] = global_rank
		}

		if i % block_size == 0 {
			rs.Blocks[i/block_size] = global_rank - last_block_rank
			// fmt.Println("block slice ", i, (i/block_size) - 1, temp_block_val)
			rs.Block_slice[(i/block_size)-1] = temp_block_val
			temp_block_val = 0
		}

		if bits[i] == true {
			temp_block_val += int(math.Pow(2, float64(block_size - (i%block_size) - 1)))
		}

		if bits[i] == true {
			global_rank++ 
		}

		// fmt.Println("tbv", temp_block_val)
	}
	// fmt.Println(block_size)
	rs.Block_slice[len(rs.Block_slice)-1] = temp_block_val

	for i := 0; i < int(math.Pow(2, float64(block_size))); i++ {
		rs.Table[i] = make([]int, block_size)

		k := i
		vec := make([]int, block_size)
		loop := 0
		for k > 0 {
			vec[block_size - loop - 1] = int(k%2)
			k = k/2
			loop++
		}

		global_rank := 0
		for j := 0; j < len(vec); j++ {
			if vec[j] == 1 {
				global_rank++
			}
			rs.Table[i][j] = global_rank
		}
	}

	return rs
}

// calculate overhead for the rank-select structure
// can use unsafe.size() but doesn't return the actual size
func (rs rs_struct) overhead() int {

	return (64 * rs.Sblock_length) + 64 + // size of superblock storing the sbox bin size 
		(2 * 64 * rs.Block_length) + 64 +  // size of block + size of block size which stores slices as integers, and the binsize of block
		(64 * len(rs.Table) * rs.Block_length) // size of table (its a map)
}

// rank1 operation on rank-select
func (rs rs_struct) rank1(i int) int {
	i_sblock := i/rs.Sblock_length
	i_block := i/rs.Block_length
	i_table := i%rs.Block_length
	
	rank := rs.Sblocks[i_sblock]
	rank += rs.Blocks[i_block]

	// fmt.Println(rs)
	// fmt.Println("i_sblock, i_block, i_table", i_sblock, i_block, i_table)

	// get val of block
	val := rs.Block_slice[i_block]
	// fmt.Println("i_sblock, i_block, i_table", i_sblock, i_block, i_table)

	// bit := rs.Bits[i_block*rs.Block_length:(i_block + 1) *rs.Block_length]
	// val := 0
	// for i := 0; i < len(bit); i++ {
	// 	tval := 0
	// 	if bit[len(bit) - i - 1] == true {
	// 		tval = 1
	// 	}
	// 	val += (tval * int(math.Pow(2, float64(i))))
	// }

	rank += rs.Table[val][i_table]
	return rank
}

// rank0 operation on rank-select
func (rs rs_struct) rank0(i int) int {
	rank := rs.rank1(i)
	return i - rank + 1
}

// select1 operation on rank-select
func (rs rs_struct) select1(i int) int {
	// fmt.Println("select1 ", i)
	start := 0
	// end := len(rs.Bits)
	end := int(math.Pow(2, math.Sqrt(float64(rs.Sblock_length*2))))
	oend := end

	found := -1
	rfound := -1

	for start < end {
		// fmt.Println("start, end ", start, end)
		mid := (start + end) /2
		rmid := rs.rank1(mid)

		if i == rmid {
			found = mid
			break
		}

		if i < rmid {
			end = mid
		} else {
			start = mid + 1
		}

		rfound = rmid
	}

	if found != -1 {
		// check if found is actually the first
		for j := found; j > 0; j-- {
			rank := rs.rank1(j) 
			if i == rank {
				found = j
			} else {
				break
			}
		}

		return found
	} else {

		if rfound > i {
			// fmt.Println("found > i")
			for j := start; j >= 0; j-- {
				rank := rs.rank0(j)
				// fmt.Println("j, rank ", j, rank)
				if i-1 == rank {
					found = j + 1
					break
				}
			}
		} else {
			// fmt.Println("found < i")
			for j := start; j < oend; j++ {
				rank := rs.rank0(j)
				// fmt.Println("j, rank ", j, rank)
				if i == rank {
					return j + 1
				}
			}
		}
	}

	return found
}

// select0 structure on rank-select
func (rs rs_struct) select0(i int) int {
	// fmt.Println("select0 ", i)
	// fmt.Println("rs ", rs)

	start := 0
	// end := len(rs.Bits)
	end := int(math.Pow(2, math.Sqrt(float64(rs.Sblock_length))))
	oend := end

	found := -1
	rfound := -1

	for start < end {
		// fmt.Println("start, end ", start, end)
		mid := (start + end) /2
		rmid := rs.rank0(mid)

		// fmt.Println("mid, rmid ", mid, rmid)

		if i == rmid {
			found = mid
			break
		}

		if i < rmid {
			end = mid
		} else {
			start = mid + 1
		}

		rfound = rmid
		// fmt.Println("ending start, end ", start, end)
	}

	// fmt.Println("found, rfound ", found, rfound)
	// fmt.Println("start, end ", start, end)

	if found != -1 {
		// check if found is actually the first
		for j := found; j > 0; j-- {
			rank := rs.rank0(j) 
			if i == rank {
				found = j
			} else {
				break
			}
		}

		return found
	} else {

		if rfound > i {
			// fmt.Println("found > i")
			for j := start; j >= 0; j-- {
				rank := rs.rank0(j)
				// fmt.Println("j, rank ", j, rank)
				if i-1 == rank {
					found = j + 1
					break
				}
			}
		} else {
			// fmt.Println("found < i")
			for j := start; j < oend; j++ {
				rank := rs.rank0(j)
				// fmt.Println("j, rank ", j, rank)
				if i == rank {
					return j + 1
				}
			}
		}

	}

	return found
}

// wavelet structure
type wt struct {
	Edges map[int]*wt
	Text string
	Bits *bitvec
	Bitmap map[string]bool
	Rs *rs_struct
	parent *wt
}

func makeWT(length int) *wt {
	wtree := new(wt)
	wtree.Edges = make(map[int]*wt)
	wtree.Text = ""
	// wtree.Bits = make([]bool, length)
	wtree.Bitmap = make(map[string]bool)
	wtree.Rs = new(rs_struct)

	return wtree
}

// creates bitvector for the given text and its right segement characters
// assumption is all left characters = 0, rights = 1
func make_bit_vector(text string, rseg []string) ([]bool, string, string) {
	bits := make([]bool, len(text))
	
	lstring := ""
	rstring := ""

	for i, r := range text {
		found := 0
		for _, a := range rseg {
			if string(r) == a {
			   found++
			   break
			}
		 }

		 if found == 1 {
			rstring += string(r)
		 } else {
			lstring += string(r)
		 }

		 if found == 0 {
			bits[i] = false
		 } else {
			bits[i] = true
		 }
		//  bits[i] = found
	}

	return bits, lstring, rstring
}

// builds the wavelet tree 
func build_wt(root *wt, text string) *wt {
	// fmt.Println("Building ", text)

	root.Text = text

	hist := make(map[string]int)

	for _, r := range text {
		hist[string(r)] += 1
	}
	
	// fmt.Println("hist - ", hist, len(hist))

	keys := make([]string, len(hist))
	count := 0
	for k := range hist {
		keys[count] = k
		count++
	}

	// fmt.Println("keys ", keys)

	sort.Strings(keys)

	// fmt.Println("after sort ", keys)
	key_len := len(keys)
	
	lchild := keys[0:key_len/2]
	for _, r := range lchild {
		root.Bitmap[string(r)] = false
	}
	
	rchild := keys[key_len/2:key_len] 
	for _, r := range rchild {
		root.Bitmap[string(r)] = true
	}

	// fmt.Println("lchild, rchild ", lchild, rchild)

	bits, lstring, rstring := make_bit_vector(text, rchild)

	// fmt.Println("bits, lstring, rstring ", bits, lstring, rstring)

	root.Bits = makeBitvec(bits)
	root.Rs = build_rank_select(bits)
	
	if len(lchild) > 1 {
		// fmt.Println("lchild > 1 ", strings.Join(lchild, ""))
		root.Edges[0] = build_wt(makeWT(len(lstring)), lstring)
		// root.Edges[0].parent = root

	} else if len(lchild) == 1 {
		// fmt.Println("lchild == 1 ", strings.Join(lchild, ""))
		root.Edges[0] = makeWT(len(lstring))
		root.Edges[0].Text = lstring
		// root.Edges[0].parent = root
		// fmt.Println("lchild == 1 ", root.edges[strings.Join(lchild, "")])
	}
	
	if len(rchild) > 1 {
		// fmt.Println("rchild > 1", strings.Join(rchild, ""))
		root.Edges[1] = build_wt(makeWT(len(rstring)), rstring)
		// root.Edges[1].parent = root
	} else if len(rchild) == 1 {
		// fmt.Println("rchild == 1 ", strings.Join(rchild, ""))
		root.Edges[1] = makeWT(len(rstring))
		root.Edges[1].Text = rstring
		// root.Edges[1].parent = root
		// fmt.Println("lchild == 1 ", root.edges[strings.Join(rchild, "")])
	}

	return root
}

// access at i 
func (wtree wt) access(i int) string {
	// fmt.Println("i", i)
	// fmt.Println("wtree", wtree)

	if len(wtree.Edges) == 0 {
		// fmt.Println("no more edges", wtree.text[0:1])
		return wtree.Text[0:1]
	}

	bit := wtree.Bits.getBitAt(i)
	// fmt.Println("bit", bit)

	if bit == uint8(0) {
		// go left
		rleft := wtree.Rs.rank0(i)
		// fmt.Println("left", rleft)
		return wtree.Edges[0].access(rleft)
	} else {
		// go right
		rright := wtree.Rs.rank1(i)
		// fmt.Println("right", rright)
		return wtree.Edges[1].access(rright)
	}
}

// rank of c, i
func (wtree wt) rank(c string, i int) int {
	// fmt.Println("c, i", c, i)
	// fmt.Println("wtree", wtree)

	if len(wtree.Edges) == 0 {
		// fmt.Println("no more edges", wtree.text[0:1])
		return i + 1
	}

	bit := wtree.Bitmap[c]
	// fmt.Println("bit", bit)
	// rank := 0

	if bit == false {
		// go left
		// fmt.Println("left", rleft)
		rleft := wtree.Rs.rank0(i)
		// fmt.Println("left", rleft)
		return wtree.Edges[0].rank(c, rleft)
	} else {
		// go right
		rright := wtree.Rs.rank1(i)
		// fmt.Println("right", rright)
		return wtree.Edges[1].rank(c, rright)
	}
}

// traverse_leaf 
func (wtree wt) traverse_leaf(c string) *wt {
	// fmt.Println("traverse leaf ", c)
	if len(wtree.Edges) == 0 {
		// fmt.Println("no more edges", wtree.text[0:1])
		return wtree.parent
	}

	bit := wtree.Bitmap[c]
	// fmt.Println("bit", bit)
	// rank := 0

	if bit == false {
		// go left
		wtree.Edges[0].parent = &wtree
		return wtree.Edges[0].traverse_leaf(c)
	} else {
		// go right
		wtree.Edges[1].parent = &wtree
		return wtree.Edges[1].traverse_leaf(c)
	}
}

func (wtree wt) iselect(c string, i int) int {
	// fmt.Println("isselect ", c, i)
	// fmt.Println("issel wtree ", wtree)
	
	isel := 0
	bit := wtree.Bitmap[c]
	// fmt.Println("bit ", bit)
	if bit == false {
		isel = wtree.Rs.select0(i)
		// fmt.Println("left isselect ", isel)
	} else {
		isel = wtree.Rs.select1(i)
		// fmt.Println("right isselect ", isel)
	}

	// fmt.Println("isel", isel)
	// fmt.Println("wtree.parent", wtree.parent)
	if wtree.parent == nil {
		// fmt.Println("is nil", )
		return isel
	}

	// nbit := 0
	// fmt.Println("wtree parent", wtree.parent.edges[1])
	// fmt.Println("wtree", &wtree)
	// if wtree.parent.edges[1] == &wtree {
	// 	fmt.Println("both are same")
	// 	nbit = 1
	// }

	return wtree.parent.iselect(c, isel)
}

// select of c,i
func (wtree wt) wtselect(c string, i int) int {
	// fmt.Println("c, i", c, i)
	// traverse to leaf
	leaf := wtree.traverse_leaf(c)

	// fmt.Println("leaf in sel ", leaf)
	// bit := leaf.bitmap[c]
	// fmt.Println("bit ", bit)

	return leaf.iselect(c, i)
}

func validate_args(args []string) bool {

	if args[0] != "help" && len(args) != 3 {
		return false
	}
	return true
}

// saves wavelet to disk
func (wtree wt) save_wt(fileName string) {
	f, err := os.Create(fileName)
	if err != nil {
		panic(err)
	}

	enc := gob.NewEncoder(f)
	err = enc.Encode(wtree)
	if err != nil {
		panic(err)
	}
	f.Close()
}

// loads wavelet from disk
func load_wt(fileName string) *wt {
	f, err := os.Open(fileName)
	if err != nil {
		panic(err)
	}
	dec := gob.NewDecoder(f)

	var wtree wt
	dec.Decode(&wtree)
	f.Close()
	// fmt.Println(wtree)

	return &wtree
}

func main() {

	// first argument is the name of the binary
	args := os.Args[1:]

	// parse the operation to perform
	switch args[0] {
		case "build":
			// wt build <input string> <output file>
			if validate_args(args) == false {
				panic("invalid arguments!")
			}

			text := args[1]

			twt := makeWT(len(text))
			twt = build_wt(twt, text)
			// fmt.Println(twt)

			twt.save_wt(args[2])

			fmt.Println("output file ", args[2], "successfully created!")
		case "access":
			// $wt access <saved wt> <access indices>
			if validate_args(args) == false {
				panic("invalid arguments!")
			}

			wtree := load_wt(args[1])
			// fmt.Println(wtree)

			file, _ := os.Open(args[2])
    		fscanner := bufio.NewScanner(file)
			for fscanner.Scan() {
				i, err := strconv.ParseInt(fscanner.Text(), 10, 32)
				if err != nil {
					panic("index error!")
				}
	
				c := wtree.access(int(i))
				fmt.Println(c)
			}
		case "rank":
			// $wt access <saved wt> <access indices>
			if validate_args(args) == false {
				panic("invalid arguments!")
			}
			
			wtree := load_wt(args[1])

			file, _ := os.Open(args[2])
    		fscanner := bufio.NewScanner(file)
			for fscanner.Scan() {
				// fmt.Println(fscanner.Text())
				words := strings.Fields(fscanner.Text())
				i, err := strconv.ParseInt(words[1], 10, 32)
				if err != nil {
					panic("index error!")
				}
	
				out := wtree.rank(words[0], int(i))
				fmt.Println(out)
			}	
		case "select":
			// $wt access <saved wt> <access indices>
			if validate_args(args) == false {
				panic("invalid arguments!")
			}
			
			wtree := load_wt(args[1])

			file, _ := os.Open(args[2])
    		fscanner := bufio.NewScanner(file)
			for fscanner.Scan() {
				// fmt.Println(fscanner.Text())
				words := strings.Fields(fscanner.Text())
				i, err := strconv.ParseInt(words[1], 10, 32)
				if err != nil {
					panic("index error!")
				}
	
				out := wtree.wtselect(words[0], int(i)-1)
				fmt.Println(out)
			}
		case "dotgraph":
			// $wt dotgraph <saved wt>
			wtree := load_wt(args[1])

			buf2 := &bytes.Buffer{}
			memviz.Map(buf2, wtree)
			fmt.Println(buf2.String())
		case "runtests":
			// $wt runtests
			fmt.Println("running task1")
			test_task1()
			fmt.Println("writing task1-size and task1-times")
			fmt.Println("running task2")
			test_task2()
			fmt.Println("writing task2-size and task2-times")
			fmt.Println("running task3")
			test_task3()
			fmt.Println("writing task3.1-times and task3.2-times")
		case "help":
			fmt.Println("wt build <input string> <output file>")
			fmt.Println("wt access <saved wt> <access indices file>")
			fmt.Println("wt rank <saved wt> <access indices file>")
			fmt.Println("wt select <saved wt> <access indices file>")
			fmt.Println("wt dotgraph <saved wt>")
			fmt.Println("\t if you hvae dot install, pipe the output")
			fmt.Println("\t\t wt dotgraph <saved wt> | dot -Tpng -o graph.png")
			fmt.Println("wt runtests")
		default:
			fmt.Println("unrecognized command!")
	}

	// bitvec := []int{1,0,0,1,0,1,1,1,0,1,0,0,1,0,1,0}
	// bitvec := []bool{true, false, false, true, false, true, true, true, false, true, false, false, true, false, true, false}
	// rs := build_rank_select(bitvec)
	// fmt.Println(rs)	

	// rank1 := rs.rank1(7)
	// rank0 := rs.rank0(4)
	// fmt.Println("rank", rank0)
	// fmt.Println("rank", rank1)

	// fmt.Println(bitvec)

	// select1 := rs.select1(6)
	// fmt.Println("select1", select1)
	// select0 := rs.select0(3)
	// fmt.Println("fselect0", select0)
	// select0 = rs.select0(4)
	// fmt.Println("fselect0", select0)	
	// select0 = rs.select0(5)
	// fmt.Println("fselect0", select0)
	// select0 = rs.select0(6)
	// fmt.Println("fselect0", select0)
	// select0 = rs.select0(7)
	// fmt.Println("fselect0", select0)

	// text := "alabar_a_la_alabarda"
	// twt := makeWT(len(text))
	// twt = build_wt(twt, text)
	// fmt.Println(twt)

	// fmt.Println("$$$$$ ACCCESS $$$$$$$")
	// c := twt.access(7)
	// fmt.Println("access ", c)

	// fmt.Println("$$$$$ RANK $$$$$$$")
	// i := twt.rank("a", 10)
	// fmt.Println("rank ", i)

	// fmt.Println("$$$$$ SELECT $$$$$$$")
	// s := twt.wtselect("a", 4)
	// fmt.Println("select ", s)

	// buf := &bytes.Buffer{}
	// memviz.Map(buf, twt)
	// fmt.Println(buf.String())
	// fmt.Println(new_wt)
	// fmt.Println("running task1")
	// test_task1()
	// fmt.Println("running task2")
	// test_task2()
	// fmt.Println("running task3")
	// test_task3()
}

// generates a random bitvector of length l
func generate_random_bitvec(l int) []bool {
	vec := make([]bool, l)
	
	for j := 0; j < l; j++ {
		vec[j] = rand.Intn(2) == 0
	}

	return vec
}

// running tests from this point
func test_task1() {
	const n int = 11

	var times [n][n]float64
	var sizes [n]int


	for i := 0; i < n; i++ {
		bsize := int(math.Pow(2, float64(i)) * 1024)
		vec := generate_random_bitvec(bsize)
		rs := build_rank_select(vec)
		sizes[i] = rs.overhead()

		for runs := 0; runs < n; runs++ {
			start := time.Now()
			// time to do n rank operations on random indices
			for j := 0; j < n; j++ {
				rs.rank1(rand.Intn(bsize))
			}
			end := time.Now().Sub(start)

			times[i][runs] = float64(end.Nanoseconds())
		}
	}

	f, err := os.Create("task1-times.json")
	if err != nil {
		panic(err)
	}

	enc := json.NewEncoder(f)
	err = enc.Encode(times)
	f.Close()

	f, err = os.Create("task1-size.json")
	if err != nil {
		panic(err)
	}

	enc = json.NewEncoder(f)
	err = enc.Encode(sizes)
	f.Close()
}

func test_task2() {
	const n int = 11

	var times [n][n]float64
	var sizes [n]int


	for i := 0; i < n; i++ {
		bsize := int(math.Pow(2, float64(i)) * 1024)
		vec := generate_random_bitvec(bsize)
		rs := build_rank_select(vec)
		sizes[i] = rs.overhead()

		for runs := 0; runs < n; runs++ {
			start := time.Now()
			// time to do n select operations on random indices
			for j := 0; j < n; j++ {
				rs.select1(rand.Intn(bsize)/3)
			}
			end := time.Now().Sub(start)

			times[i][runs] = float64(end.Nanoseconds())
		}
	}

	f, err := os.Create("task2-times.json")
	if err != nil {
		panic(err)
	}

	enc := json.NewEncoder(f)
	err = enc.Encode(times)
	f.Close()

	f, err = os.Create("task2-size.json")
	if err != nil {
		panic(err)
	}

	enc = json.NewEncoder(f)
	err = enc.Encode(sizes)
	f.Close()
}

func generate_random_string(l int, chars []string) string {
	result := ""

	for i := 0; i < l; i++ {
		rchar := chars[rand.Intn(len(chars)-1)]
		result += rchar
	}

	return result
}

func test_task3() {
	const n int = 5

	// part 1 - rank and select with string length
	var times [n][2*n]float64
	chars := []string{"a", "b", "c", "d", "e", "f", "g"}

	for i := 0; i < n; i++ {
		bsize := int(math.Pow(2, float64(i)) * 1024)
		text := generate_random_string(bsize, chars)

		twt := makeWT(len(text))
		twt = build_wt(twt, text)

		for runs := 0; runs < n; runs++ {
			j := rand.Intn(20)
			start := time.Now()
			// time to do n rank operations on random indices
			twt.rank(chars[rand.Intn(len(chars)-1)], rand.Intn(bsize))
			end := time.Now().Sub(start)

			times[i][runs] = float64(end.Nanoseconds())

			start = time.Now()
			// time to do n rank operations on random indices
			twt.wtselect(chars[rand.Intn(len(chars)-1)], (j/2) + 1)
			end = time.Now().Sub(start)

			times[i][n + runs] = float64(end.Nanoseconds())
		}
	}

	f, err := os.Create("task3.1-times.json")
	if err != nil {
		panic(err)
	}

	enc := json.NewEncoder(f)
	err = enc.Encode(times)
	f.Close()

	fmt.Println("part 2")
	
	const n2 int = 8
	var times2 [n2][2*n2]float64

	for i := 3; i < n2; i++ {
		bsize := int(64 * 1024)
		text := generate_random_string(bsize, chars[0:i])
		twt := makeWT(len(text))
		twt = build_wt(twt, text)

		for runs := 0; runs < n2; runs++ {
			j := rand.Intn(20)
			start := time.Now()
			// time to do n rank operations on random indices
			twt.rank(chars[rand.Intn(len(chars)-1)], rand.Intn(bsize))
			end := time.Now().Sub(start)

			times2[i][runs] = float64(end.Nanoseconds())

			start = time.Now()
			// time to do n rank operations on random indices
			twt.wtselect(chars[rand.Intn(len(chars)-1)], (j/2) + 1)
			end = time.Now().Sub(start)

			times2[i][n2 + runs] = float64(end.Nanoseconds())
		}
	}

	f, err = os.Create("task3.2-times.json")
	if err != nil {
		panic(err)
	}

	enc = json.NewEncoder(f)
	err = enc.Encode(times2)
	f.Close()
}