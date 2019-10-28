package main 

import (
	"fmt"
	"math/rand"
	"math"
	"os"
	"bufio"
	// "io"
	"encoding/gob"
	"encoding/json"
	// "encoding/binary"
	// "io/ioutil"
	"sort"
	"strings"
	"strconv"
	"bytes"
	// "reflect"
	// "unsafe"
	// "runtime"
	"time"
	"github.com/bradleyjkemp/memviz"
	// "github.com/go-restruct/restruct"
)

// probably unnecessary
// type bvec struct {
// 	bits []bool
// 	length int
// }

// func makebinVector(length int, randomize bool) {
// 	vec := new(bvec)
// 	vec.length = length
// 	vec.bits = make([]bool, length)
// 	if randomize {
// 		for j := 0; j < length; j++ {
// 			vec.bits[j] = rand.Int(1)
// 		}
// 	}
// }

type rs_struct struct {
	Bits []bool
	Sblocks []int
	Sblock_length int
	Blocks []int
	Block_length int
	Table map[int][]int
}

func build_rank_select(bits []bool) *rs_struct {
	l := float64(len(bits))
	sblock_size := int(math.Pow(math.Log2(l), 2)/2)
	block_size := int(math.Log2(l)/2)

	rs := new(rs_struct)
	rs.Bits = bits
	rs.Sblocks = make([]int, int(math.Ceil(l/float64(sblock_size))))
	rs.Sblock_length = sblock_size
	rs.Blocks = make([]int, int(math.Ceil(l/float64(block_size))))
	rs.Block_length = block_size
	rs.Table = make(map[int][]int)

	global_rank := 0
	last_block_rank := 0

	if bits[0] == true {
		global_rank++
	}
	rs.Sblocks[0] = 0
	rs.Blocks[0] = 0

	for i := 1; i < len(bits); i++ {
		if i % sblock_size == 0 {
			last_block_rank = global_rank
			rs.Sblocks[i/sblock_size] = global_rank
		}

		if i % block_size == 0 {
			rs.Blocks[i/block_size] = global_rank - last_block_rank
		}

		if bits[i] == true {
			global_rank++ 
		}
	}

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

func (rs rs_struct) overhead() int {
	// fmt.Println("rs ", rs.Sblock_length, rs.Block_length, len(rs.Table))

	// return int(unsafe.Sizeof(rs))
	return (64 * rs.Sblock_length) +  64 + (64 * rs.Block_length) + 64 + (64 * len(rs.Table) * rs.Block_length)
	// return len(rs.Sblocks) + int(unsafe.Sizeof(rs.Sblock_length)) + 
	// 		int(unsafe.Sizeof(rs.Block_length)) + int(unsafe.Sizeof(rs.Blocks))*len(rs.Blocks) + int(unsafe.Sizeof(rs.Table))
}

func (rs rs_struct) rank1(i int) int {
	i_sblock := i/rs.Sblock_length
	i_block := i/rs.Block_length
	i_table := i%rs.Block_length
	
	rank := rs.Sblocks[i_sblock]
	rank += rs.Blocks[i_block]

	// fmt.Println(rs)
	// fmt.Println("i_sblock, i_block, i_table", i_sblock, i_block, i_table)
	
	bit := rs.Bits[i_block*rs.Block_length:(i_block + 1) *rs.Block_length]
	val := 0
	for i := 0; i < len(bit); i++ {
		tval := 0
		if bit[len(bit) - i - 1] == true {
			tval = 1
		}
		val += (tval * int(math.Pow(2, float64(i))))
	}

	rank += rs.Table[val][i_table]
	return rank - 1
}

func (rs rs_struct) rank0(i int) int {
	rank := rs.rank1(i)
	return i - rank - 1
}

func (rs rs_struct) select1(i int) int {
	// fmt.Println("select1 ", i)
	start := 0
	end := len(rs.Bits)

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
			for j := start; j < len(rs.Bits); j++ {
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

func (rs rs_struct) select0(i int) int {
	// fmt.Println("select0 ", i)
	// fmt.Println("rs ", rs)

	start := 0
	end := len(rs.Bits)

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
			for j := start; j < len(rs.Bits); j++ {
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

type wt struct {
	Edges map[int]*wt
	Text string
	Bits []bool
	Bitmap map[string]bool
	Rs *rs_struct
	parent *wt
}

func makeWT(length int) *wt {
	wtree := new(wt)
	wtree.Edges = make(map[int]*wt)
	wtree.Text = ""
	wtree.Bits = make([]bool, length)
	wtree.Bitmap = make(map[string]bool)
	wtree.Rs = new(rs_struct)

	return wtree
}

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

	root.Bits = bits
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

func (wtree wt) access(i int) string {
	// fmt.Println("i", i)
	// fmt.Println("wtree", wtree)

	if len(wtree.Edges) == 0 {
		// fmt.Println("no more edges", wtree.text[0:1])
		return wtree.Text[0:1]
	}

	bit := wtree.Bits[i]
	// fmt.Println("bit", bit)

	if bit == false {
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

func generate_random_bitvec(l int) []bool {
	vec := make([]bool, l)
	
	for j := 0; j < l; j++ {
		vec[j] = rand.Intn(2) == 0
	}

	return vec
}

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