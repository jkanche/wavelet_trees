package main 

import (
	"fmt"
	// "math/rand"
	"math"
	"sort"
	"strings"
	"bytes"
	"github.com/bradleyjkemp/memviz"
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
	bits []int
	sblocks []int
	sblock_length int
	blocks []int
	block_length int
	table map[int][]int
}

func build_rank_select(bits []int) *rs_struct {
	l := float64(len(bits))
	sblock_size := int(math.Pow(math.Log2(l), 2)/2)
	block_size := int(math.Log2(l)/2)

	rs := new(rs_struct)
	rs.bits = bits
	rs.sblocks = make([]int, int(math.Ceil(l/float64(sblock_size))))
	rs.sblock_length = sblock_size
	rs.blocks = make([]int, int(math.Ceil(l/float64(block_size))))
	rs.block_length = block_size
	rs.table = make(map[int][]int)

	global_rank := 0
	last_block_rank := 0

	if bits[0] == 1 {
		global_rank++
	}
	rs.sblocks[0] = 0
	rs.blocks[0] = 0

	for i := 1; i < len(bits); i++ {
		if i % sblock_size == 0 {
			last_block_rank = global_rank
			rs.sblocks[i/sblock_size] = global_rank
		}

		if i % block_size == 0 {
			rs.blocks[i/block_size] = global_rank - last_block_rank
		}

		if bits[i] == 1 {
			global_rank++ 
		}
	}

	for i := 0; i < int(math.Pow(2, float64(block_size))); i++ {
		rs.table[i] = make([]int, block_size)

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
			rs.table[i][j] = global_rank
		}
	}

	return rs
}

func (rs rs_struct) rank1(i int) int {
	i_sblock := i/rs.sblock_length
	i_block := i/rs.block_length
	i_table := i%rs.block_length
	
	rank := rs.sblocks[i_sblock]
	rank += rs.blocks[i_block]
	
	bit := rs.bits[i_block*rs.block_length:(i_block + 1) *rs.block_length]
	val := 0
	for i := 0; i < len(bit); i++ {
		val += (bit[len(bit) - i - 1] * int(math.Pow(2, float64(i))))
	}

	rank += rs.table[val][i_table]
	return rank
}

func (rs rs_struct) rank0(i int) int {
	rank := rs.rank1(i)
	return i - rank 
}

func (rs rs_struct) select1(i int) int {
	start := 0
	end := len(rs.bits)

	found := -1
	rfound := -1

	for start < end {
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
			fmt.Println("found > i")
			for j := start; j >= 0; j-- {
				rank := rs.rank0(j)
				fmt.Println("j, rank ", j, rank)
				if i-1 == rank {
					found = j + 1
					break
				}
			}
		} else {
			fmt.Println("found < i")
			for j := start; j < len(rs.bits); j++ {
				rank := rs.rank0(j)
				fmt.Println("j, rank ", j, rank)
				if i == rank {
					return j + 1
				}
			}
		}
	}

	return found
}

func (rs rs_struct) select0(i int) int {
	fmt.Println("select0 ", i)
	fmt.Println("rs ", rs)

	start := 0
	end := len(rs.bits)

	found := -1
	rfound := -1

	for start < end {
		fmt.Println("start, end ", start, end)
		mid := (start + end) /2
		rmid := rs.rank0(mid)

		fmt.Println("mid, rmid ", mid, rmid)

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
		fmt.Println("endging start, end ", start, end)
	}

	fmt.Println("found, rfound ", found, rfound)
	fmt.Println("start, end ", start, end)

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
			fmt.Println("found > i")
			for j := start; j >= 0; j-- {
				rank := rs.rank0(j)
				fmt.Println("j, rank ", j, rank)
				if i-1 == rank {
					found = j + 1
					break
				}
			}
		} else {
			fmt.Println("found < i")
			for j := start; j < len(rs.bits); j++ {
				rank := rs.rank0(j)
				fmt.Println("j, rank ", j, rank)
				if i == rank {
					return j + 1
				}
			}
		}

	}

	return found
}

type wt struct {
	edges map[int]*wt
	text string
	bits []int
	bitmap map[string]int
	rs *rs_struct
	parent *wt
}

func makeWT(length int) *wt {
	wtree := new(wt)
	wtree.edges = make(map[int]*wt)
	wtree.text = ""
	wtree.bits = make([]int, length)
	wtree.bitmap = make(map[string]int)
	wtree.rs = new(rs_struct)

	return wtree
}

func make_bit_vector(text string, rseg []string) ([]int, string, string) {
	bits := make([]int, len(text))
	
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


		 bits[i] = found
	}

	return bits, lstring, rstring
}


func build_wt(root *wt, text string) *wt {
	fmt.Println("Building ", text)

	root.text = text

	hist := make(map[string]int)

	for _, r := range text {
		hist[string(r)] += 1
	}
	
	fmt.Println("hist - ", hist, len(hist))

	keys := make([]string, len(hist))
	count := 0
	for k := range hist {
		keys[count] = k
		count++
	}

	fmt.Println("keys ", keys)

	sort.Strings(keys)

	fmt.Println("after sort ", keys)
	key_len := len(keys)
	
	lchild := keys[0:key_len/2]
	for _, r := range lchild {
		root.bitmap[string(r)] = 0
	}
	
	rchild := keys[key_len/2:key_len] 
	for _, r := range rchild {
		root.bitmap[string(r)] = 1
	}

	fmt.Println("lchild, rchild ", lchild, rchild)

	bits, lstring, rstring := make_bit_vector(text, rchild)

	fmt.Println("bits, lstring, rstring ", bits, lstring, rstring)

	root.bits = bits
	root.rs = build_rank_select(bits)
	
	if len(lchild) > 1 {
		fmt.Println("lchild > 1 ", strings.Join(lchild, ""))
		root.edges[0] = build_wt(makeWT(len(lstring)), lstring)
		root.edges[0].parent = root

	} else if len(lchild) == 1 {
		fmt.Println("lchild == 1 ", strings.Join(lchild, ""))
		root.edges[0] = makeWT(len(lstring))
		root.edges[0].text = lstring
		root.edges[0].parent = root
		// fmt.Println("lchild == 1 ", root.edges[strings.Join(lchild, "")])
	}
	
	if len(rchild) > 1 {
		fmt.Println("rchild > 1", strings.Join(rchild, ""))
		root.edges[1] = build_wt(makeWT(len(rstring)), rstring)
		root.edges[1].parent = root
	} else if len(rchild) == 1 {
		fmt.Println("rchild == 1 ", strings.Join(rchild, ""))
		root.edges[1] = makeWT(len(rstring))
		root.edges[1].text = rstring
		root.edges[1].parent = root
		// fmt.Println("lchild == 1 ", root.edges[strings.Join(rchild, "")])
	}

	return root
}

func (wtree wt) access(i int) string {
	fmt.Println("i", i)
	fmt.Println("wtree", wtree)

	if len(wtree.edges) == 0 {
		fmt.Println("no more edges", wtree.text[0:1])
		return wtree.text[0:1]
	}

	bit := wtree.bits[i]
	fmt.Println("bit", bit)

	if bit == 0 {
		// go left
		// fmt.Println("left", rleft)
		rleft := wtree.rs.rank0(i)
		fmt.Println("left", rleft)
		return wtree.edges[0].access(rleft)
	} else {
		// go right
		rright := wtree.rs.rank1(i)
		fmt.Println("right", rright)
		return wtree.edges[1].access(rright)
	}
}

func (wtree wt) rank(c string, i int) int {
	fmt.Println("c, i", c, i)
	fmt.Println("wtree", wtree)

	if len(wtree.edges) == 0 {
		fmt.Println("no more edges", wtree.text[0:1])
		return i
	}

	bit := wtree.bitmap[c]
	fmt.Println("bit", bit)
	// rank := 0

	if bit == 0 {
		// go left
		// fmt.Println("left", rleft)
		rleft := wtree.rs.rank0(i)
		fmt.Println("left", rleft)
		return wtree.edges[0].rank(c, rleft)
	} else {
		// go right
		rright := wtree.rs.rank1(i)
		fmt.Println("right", rright)
		return wtree.edges[1].rank(c, rright)
	}

}

func (wtree wt) traverse_leaf(c string) *wt {
	fmt.Println("traverse leaf ", c)
	if len(wtree.edges) == 0 {
		fmt.Println("no more edges", wtree.text[0:1])
		return wtree.parent
	}

	bit := wtree.bitmap[c]
	fmt.Println("bit", bit)
	// rank := 0

	if bit == 0 {
		// go left
		return wtree.edges[0].traverse_leaf(c)
	} else {
		// go right
		return wtree.edges[1].traverse_leaf(c)
	}
}

func (wtree wt) iselect(c string, i int) int {
	fmt.Println("isselect ", c, i)
	fmt.Println("issel wtree ", wtree)
	
	isel := 0
	bit := wtree.bitmap[c]
	fmt.Println("bit ", bit)
	if bit == 0 {
		isel = wtree.rs.select0(i)
		fmt.Println("left isselect ", isel)
	} else {
		isel = wtree.rs.select1(i)
		fmt.Println("right isselect ", isel)
	}

	fmt.Println("isel", isel)
	fmt.Println("wtree.parent", wtree.parent)
	if wtree.parent == nil {
		fmt.Println("is nil", )
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
	fmt.Println("c, i", c, i)
	// traverse to leaf
	leaf := wtree.traverse_leaf(c)

	fmt.Println("leaf in sel ", leaf)
	// bit := leaf.bitmap[c]
	// fmt.Println("bit ", bit)

	return leaf.iselect(c, i)
}


func main() {
	bitvec := []int{1,0,0,1,0,1,1,1,0,1,0,0,1,0,1,0}
	rs := build_rank_select(bitvec)
	fmt.Println(rs)	

	rank1 := rs.rank1(7)
	rank0 := rs.rank0(4)
	fmt.Println("rank", rank0)
	fmt.Println("rank", rank1)

	fmt.Println(bitvec)

	select1 := rs.select1(6)
	fmt.Println("select1", select1)
	select0 := rs.select0(3)
	fmt.Println("fselect0", select0)
	select0 = rs.select0(4)
	fmt.Println("fselect0", select0)	
	select0 = rs.select0(5)
	fmt.Println("fselect0", select0)
	select0 = rs.select0(6)
	fmt.Println("fselect0", select0)
	select0 = rs.select0(7)
	fmt.Println("fselect0", select0)

	text := "alabar_a_la_alabarda"
	twt := makeWT(len(text))
	twt = build_wt(twt, text)
	fmt.Println(twt)

	fmt.Println("$$$$$ ACCCESS $$$$$$$")
	c := twt.access(7)
	fmt.Println("access ", c)

	fmt.Println("$$$$$ RANK $$$$$$$")
	i := twt.rank("a", 10)
	fmt.Println("rank ", i)

	fmt.Println("$$$$$ SELECT $$$$$$$")
	s := twt.wtselect("a", 4)
	fmt.Println("select ", s)

	buf := &bytes.Buffer{}
	memviz.Map(buf, twt)
	// fmt.Println(buf.String())


	// fmt.Println(new_wt)
}