// Хоровод. Задача о гамильтоновом цикле в двудольном графе. Алгоритм Бьёрклунда

// Соколовский Роман - 2025 г.

package main

import (
	"fmt"
	"math/rand"
)

// n - количество вершин (2 <= n <= 50)
var n int

// G - двунаправленный двудольный граф
var G [][]uint8

// s - специальная вершина
var s int

// k - степень конечного поля GF(2^k) (2 <= k <= 8)
var k int

// irredpolys - неприводимые полиномы над полем k-ой степени
// https://www.jjj.de/mathdata/all-irredpoly.txt
var irredpolys [7]uint16 = [7]uint16{
	0b111,       // 2,1,0
	0b1011,      // 3,1,0
	0b10011,     // 4,1,0
	0b100101,    // 5,2,0
	0b1000011,   // 6,1,0
	0b10000011,  // 7,1,0
	0b100011100, // 8,4,3,2,0
}

var pows_gf2 []uint8
var logs_gf2 []int

func generate_gf2() {
	power := 1 << k
	pows_gf2 = make([]uint8, power)
	logs_gf2 = make([]int, power)

	pows_gf2[0] = 1
	logs_gf2[0] = -1
	logs_gf2[1] = 0

	for i := 1; i < power-1; i++ {
		x := uint16(pows_gf2[i-1]) << 1
		if x&(1<<k) != 0 {
			x ^= uint16(irredpolys[k-2])
		}
		pows_gf2[i] = uint8(x)
		logs_gf2[pows_gf2[i]] = i
	}

	pows_gf2[power-1] = 1
}

func mul_gf(a, b uint8) uint8 {
	if a == 0 || b == 0 {
		return 0
	}
	r := logs_gf2[a] + logs_gf2[b]
	mod := len(pows_gf2) - 1
	if r >= mod {
		r -= mod
	}
	return pows_gf2[r]
}

func div_gf(a, b uint8) uint8 {
	if b == 0 {
		panic("division by zero")
	}
	if a == 0 {
		return 0
	}
	r := logs_gf2[a] - logs_gf2[b]
	mod := len(pows_gf2) - 1
	if r < 0 {
		r += mod
	}
	return pows_gf2[r]
}

func rand_gf(neq ...uint8) uint8 {
	shift := 1 << k
	var r uint8
	for {
		r = uint8(rand.Intn(shift))
		skip := false
		for _, x := range neq {
			if r == x {
				skip = true
				break
			}
		}
		if !skip {
			return r
		}
	}
}

func permanent(A [][]uint8) uint8 {
	B := make([][]uint8, len(A))
	for i := range A {
		B[i] = make([]uint8, len(A))
		copy(B[i], A[i])
	}

	for i := range B {
		if B[i][i] == 0 {
			for j := i + 1; j < len(B); j++ {
				if B[j][i] != 0 {
					B[i], B[j] = B[j], B[i]
					break
				}
			}
		}
		if B[i][i] == 0 {
			return 0
		}

		for j := i + 1; j < len(B); j++ {
			if B[j][i] != 0 {
				m := div_gf(B[j][i], B[i][i])
				for k := i; k < len(B); k++ {
					B[j][k] ^= mul_gf(m, B[i][k])
				}
			}
		}
	}

	perm := uint8(1)
	for i := range B {
		perm = mul_gf(perm, B[i][i])
	}
	return perm
}

func hamiltonicity_bipartite() bool {
	// Берем k из условия 2^k > c*n
	c := 2
	for i := 10; i > 0; i-- {
		if (c*n)&(1<<i) > 0 {
			k = i + 1
			break
		}
	}

	generate_gf2()

	// Выбираем специальную вершину, принадлежащую V1
	s = 0

	// Формируем множетсва V1 и V2 по долям
	V1, V2 := make([]int, n/2), make([]int, n/2)
	for i := range n / 2 {
		V1[i] = i
		V2[i] = n/2 + i
	}

	// Собираем множество маркировок
	L := V2

	// Формируем матрицу N, элементы которой
	// являются N(u, v) - подмножествами (масками) V2,
	// состоящими из вершин, соединённых с вершинами
	// u и v из V1
	N := make([][]uint32, len(V1))
	for i := range len(V1) {
		N[i] = make([]uint32, len(V1))
	}

	// Считаем количество ребер между долями
	var transitions_amount int

	for u := range len(V1) {
		for v := range len(V1) {
			if u == v {
				continue
			}
			for w := range len(V1) {
				if G[u][w+len(V1)] > 0 && G[v][w+len(V1)] > 0 {
					transitions_amount += 1
					N[u][v] |= (1 << w)
				}
			}
		}
	}

	if transitions_amount < n {
		return false
	}

	// Находим значение полинома в разных точках
	for range n {
		// LABELED CYCLE COVER SUM
		var lccs uint8

		// Вводим переменные x_{u,v} для арок в G и присваиваем им случайные значения
		VARS := make([][]uint8, n)
		for i := range n {
			VARS[i] = make([]uint8, n)
		}

		var r uint8

		// Присваиваем значения для переменных x_{u,v}
		for i := range n - 1 {
			for j := n - 1; j > i; j-- {
				if G[i][j] > 0 {
					r = rand_gf(0)
					VARS[i][j] = r
					VARS[j][i] = r
				}
			}
		}

		// Делаем так, чтобы x_{u,v} != x_{v,u} при u == s || v == s
		for i := n - 1; i >= 0; i-- {
			if VARS[i][s] == 0 || i == s {
				continue
			}
			if i < s {
				VARS[s][i] = rand_gf(VARS[i][s], 0)
			} else {
				VARS[i][s] = rand_gf(VARS[s][i], 0)
			}
		}

		// Ищем все поднможества маркировок Y \subseteq L
		L_subsets_amount := uint32(1 << len(L))
		for Y_mask := uint32(1); Y_mask < L_subsets_amount; Y_mask++ {
			// Инициализируем матрицу под перманентом
			T := make([][]uint8, len(V1))
			for i := range len(V1) {
				T[i] = make([]uint8, len(V1))
			}

			// Находим коффициенты для матрицы T
			for u := range len(V1) {
				for v := range len(V1) {
					if u == v {
						continue
					}
					Z_mask := N[u][v] & Y_mask
					for i := range len(V1) {
						if Z_mask&(1<<i) > 0 {
							T[u][v] ^= mul_gf(VARS[u][i+len(V1)], VARS[i+len(V1)][v])
						}
					}
				}
			}

			lccs ^= permanent(T)
		}

		if lccs > 0 {
			return true
		}

		lccs = 0
	}

	return false
}

func main() {
	// K - количество ребёр
	var K int

	fmt.Scan(&n, &K)

	G = make([][]uint8, n)
	for i := 0; i < n; i++ {
		G[i] = make([]uint8, n)
	}

	// U1, U2 - множества вершин в графе (|U1| = |U2| = n/2)
	U1, U2 := make([]string, n/2), make([]string, n/2)

	// a, b - вершины V1 и V2 соответственно
	var a, b string

	// p, q - вспомогательные счётчики для составления графа
	var p, q int

	for range K {
		fmt.Scan(&a, &b)

		for i := range U1 {
			if (U1[i] == "") || (U1[i] == a) {
				if U1[i] == "" {
					U1[i] = a
				}
				p = i
				break
			}
		}

		for j := range U2 {
			if (U2[j] == "") || (U2[j] == b) {
				if U2[j] == "" {
					U2[j] = b
				}
				q = j
				break
			}
		}

		G[p][q+n/2] = 1
		G[q+n/2][p] = 1
	}

	yes := hamiltonicity_bipartite()

	if yes {
		fmt.Println("yes")
	} else {
		fmt.Println("no")
	}
}
