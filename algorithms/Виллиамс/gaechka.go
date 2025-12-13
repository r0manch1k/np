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

// Считает количество выполненных ограничений при присваиваниях Li и Lj
//
// В нашем случае: Считает количество переходных ребёр при данных
// раскрасках Li и Lj в подмножетсвах Vi и Vj графа G
//
// Параметры i и j нужны для определения подмножетсва вершин в
// графе G (т.к. мы просто разбили их, поставив две "перегородки", то достаточно индекса)
//
// P.S. Работает примерно за Θ(n^2/9), если не считать сдвиги. Пока что-то быстрее не придумал
// Еще можно прикрутить кэширование
func w(Li int, Lj int, i int, j int) uint8 {
	var transitions uint8
	// Вспомогательные переменные для оптимизации подсчёта
	var pshift, qshift int
	// Количество вершин в подмножестве G
	K := n / 3
	for p := i * K; p < (i+1)*K; p++ {
		pshift = p - i*K
		for q := j * K; q < (j+1)*K; q++ {
			qshift = q - j*K
			if G[p][q] && ((1<<pshift)&Li > 0) != ((1<<qshift)&Lj > 0) {
				transitions += 1
			}
		}
	}
	if i == j {
		transitions /= 2
	}
	return transitions
}

// Ищет первый попавшийся треугольник в булевой матрице A
// Возвращает отсортированный массив индексов вершин из разных долей
func triangle(A [][]bool) []int {
	for i := range len(A) {
		for j := i + 1; j < len(A); j++ {
			if !A[i][j] {
				continue
			}
			for k := j + 1; k < len(A); k++ {
				if A[i][k] && A[j][k] {
					return []int{i, j, k}
				}
			}
		}
	}
	return nil
}

// Находит максимальный разрез, возвращая три маски для каждого поднможества вершин из G
func maxcut() []int {
	// Суммарное количество вершин (присваиваний/раскрасок) в долях графа H
	K := 3 * (1 << (n / 3))

	// Трёхдольный граф H
	H := make([][]uint8, K)
	for i := range K {
		H[i] = make([]uint8, K)
	}

	// Размер доли в H
	var H_part_size int = 1 << (n / 3)

	// Вспомогательные переменные для хранения индексов
	var a, b int

	// Находим веса H вариантом из статьи
	for j := range 3 {
		for l := j + 1; l < 3; l++ {
			for Lj := range H_part_size {
				a = j*H_part_size + Lj
				for Ll := range H_part_size {
					b = l*H_part_size + Ll
					if j > 0 {
						H[a][b] = w(Lj, Ll, j, l) // i23
					} else if (j == 0) && (l > 1) {
						H[a][b] = w(Ll, Ll, l, l) + w(Lj, Ll, j, l) // i12
					} else {
						H[a][b] = w(Lj, Lj, j, j) + w(Ll, Ll, l, l) + w(Lj, Ll, j, l) // i13

					}
					H[b][a] = H[a][b]
				}
			}
		}
	}

	// Булевая матрица смежности для H при i12, i13 и i23
	Hi := make([][]bool, K)
	for i := range K {
		Hi[i] = make([]bool, K)
	}

	// Здесь можно улучшить, по-умному перебирая решения i12 + i13 + i23 = N, N \in [m]
	for N := m; N >= 0; N-- {
		for i12 := m; i12 >= 0; i12-- {
			for i13 := m; i13 >= 0; i13-- {
				for i23 := m; i23 >= 0; i23-- {
					if (i12 + i13 + i23) != N {
						continue
					}
					// Заполняем матрицу с конкретными i12, i13 и i23
					for j := range 3 {
						for l := j + 1; l < 3; l++ {
							for Lj := range H_part_size {
								a = j*H_part_size + Lj
								for Ll := range H_part_size {
									b = l*H_part_size + Ll
									if j > 0 {
										Hi[a][b] = H[a][b] == uint8(i23)
									} else if (j == 0) && (l > 1) {
										Hi[a][b] = H[a][b] == uint8(i13)
									} else {
										Hi[a][b] = H[a][b] == uint8(i12)
									}
									H[b][a] = H[a][b]
								}
							}
						}
					}

					tr := triangle(Hi)
					if tr != nil {
						return tr
					}
				}
			}
		}
	}

	return nil
}

func main() {
	// Исходное количество вершин
	var K int

	fmt.Scan(&K)

	// Делаем количество вершин кратным трём
	n = (K + 2) / 3 * 3

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
		G[v-1][u-1] = true
		m += 1
	}

	if K < 3 {
		fmt.Println("1")
		return
	}

	partition := maxcut()

	// Часть, к которой принадлежит первая вершина (её цвет)
	color1 := partition[0] & 1

	// Вспомогательная переменная для вывода веришн
	first := true

	for i, mask := range partition {
		for j := range n / 3 {
			if (mask>>j)&1 == color1 {
				if !first {
					fmt.Print(" ")
				}
				first = false
				fmt.Print(i*(n/3) + j + 1)
			}
		}

	}
}
