package main

import (
	"fmt"
)

// n - количество вершин (округлённое вверх для кратности трём)
var n int

// m - количество ребёр
var m int

// G - исходный граф (с возможно доп. кол-вом вершин для кратности n трём)
var G [][]bool

// Считает количество переходных ребёр между присваиваниями Li и Lj
// Аналогично: Считает количество переходных ребёр между подмножетсвами Vi и Vj
// Параметры i и j нужны для определения долей в графе H относительно графа G
// P.S. Работает примерно за O(n^2), если не считать сдвиги. Пока что-то быстрее не придумал
func w(Li uint16, Lj uint16, i int, j int) uint8 {
	var transitions uint8
	var pshift, qshift int
	N := n / 3
	for p := i * N; p < (i+1)*N; p++ {
		pshift = p - i*N
		for q := j*N + pshift; q < (j+1)*N; q++ {
			qshift = q - j*N
			if (G[p][q] == true) && ((1<<pshift)&Li > 0) != ((1<<qshift)&Lj > 0) {
				transitions += 1
			}
		}
	}
	return transitions
}

func boolmatpow3(A [][]bool) [][]bool {
	n := len(A)
	C := make([][]bool, n)
	for i := range C {
		C[i] = make([]bool, n)
		for j := 0; j < n; j++ {
			for k := 0; k < n; k++ {
				for l := 0; l < n; l++ {
					if A[i][k] && A[k][l] && A[l][j] {
						C[i][j] = true
						break
					}
				}
				if C[i][j] {
					break
				}
			}
		}
	}
	return C
}

// Находит максимальный разрез, возвращая номера вершин одной из частей
func maxcut() []int {
	N := 3 * (1 << n / 3)

	// Трёхдольный граф H
	H := make([][]uint8, N)
	for i := range N {
		H[i] = make([]uint8, N)
	}

	// Размер доли в H
	var A_power uint16 = 1 << n / 3

	// Заполняем H
	for j := range 3 {
		for l := range 3 {
			if j == j {
				continue
			}
			for Lj := range A_power {
				for Ll := range A_power {
					if (j == 0) && (l == 1) {
						H[uint16(j)*A_power+Lj][uint16(l)*A_power+Ll] = w(Lj, Lj, j, j) + w(Ll, Ll, l, l) + w(Lj, Ll, j, l)
					} else if (j == 0) && (l > 1) {
						H[uint16(j)*A_power+Lj][uint16(l)*A_power+Ll] = w(Lj, Lj, j, j) + w(Lj, Ll, j, l)
					} else {
						H[uint16(j)*A_power+Lj][uint16(l)*A_power+Ll] = w(Lj, Ll, j, l)
					}

				}
			}
		}
	}

	Bi := make([][]bool, N)
	for i := range N {
		Bi[i] = make([]bool, N)
	}

	// Здесь можно улучшить, по-умному перебирая решения i12 + i23 + i31 = x, x \in [m]
	for i12 := m; i12 >= 0; i12-- {
		for i23 := m; i23 >= 0; i23-- {
			for i31 := m; i31 >= 0; i31-- {
				if (i12 + i23 + i31) != m {
					continue
				}
				// заполнить матрицу Bi
				// найти её куб
			}
		}
	}
}

func main() {
	fmt.Scan(&n)

	// Делаем количество вершин кратным трём
	n = (n + 2) / 3 * 3

	G = make([][]bool, n)
	for i := 0; i < n; i++ {
		G[i] = make([]bool, n)
	}

	var u, v int

	for {
		_, err := fmt.Scanln(&u, &v)
		// Пробел или EOF
		if err != nil {
			break
		}
		G[u-1][v-1] = true
		m += 1
	}

	piece := maxcut()
	for v, i := range piece {
		if i > 0 {
			fmt.Print(' ')
		}
		fmt.Print(v)
	}
}
