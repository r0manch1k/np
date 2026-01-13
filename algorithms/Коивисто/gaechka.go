// Гаечка. Задача о максимальном разрезе в графе. Алгоритм Коивисто

package main

import (
	"fmt"
	"math/big"
)

// n - количество вершин
var n int

// m - количество ребёр
var m int

// G - исходный граф
var G [][]bool

// Максимальный вес ограничения (в нашем случае, ребро либо переходое, либо нет)
var R int = 1

// Максимальный суммарный вес ограничений (в нашем случае, сколько рёбер может быть переходными)
var M int

// Количество бит, достаточное для кодирования количества выполненных ограничений (в нашем случае, переходных ребёр)
var l int

// Возвращает количество переходных ребёр между вершинами I и J
// при их раскрасках xI и xJ соответственно
func w(xI uint64, xJ uint64, I []int, J []int) int {
	var transitions int

	// Если множества вершин I и J равны, то необходимо поделить
	// результат пополам из-за специфики реализации
	var ii bool

	for i, u := range I {
		for j, v := range J {
			if !ii && (u == v) {
				ii = true
			}
			if G[u][v] && ((1<<i)&xI > 0) != ((1<<j)&xJ > 0) {
				transitions += 1
			}
		}
	}

	if ii && transitions > 0 {
		transitions /= 2
	}

	return transitions
}

// Умножает две матрицы с элементами *big.Int
//
// Если параметр T=true, то вычисляется A x B^T
func matmul(A, B [][]*big.Int, T bool) [][]*big.Int {
	N := len(A)

	D := make([][]*big.Int, N)
	for i := 0; i < N; i++ {
		D[i] = make([]*big.Int, N)
		for j := 0; j < N; j++ {
			D[i][j] = new(big.Int)
		}
	}

	tmp := new(big.Int)

	for i := 0; i < N; i++ {
		for k := 0; k < N; k++ {
			aik := A[i][k]
			if aik.Sign() == 0 {
				continue
			}

			for j := 0; j < N; j++ {
				var bkj *big.Int
				if T {
					bkj = B[j][k]
				} else {
					bkj = B[k][j]
				}

				if bkj.Sign() == 0 {
					continue
				}

				tmp.Mul(aik, bkj)
				D[i][j].Add(D[i][j], tmp)
			}
		}
	}

	return D
}

// Вычисляет скалярное произведение матриц с элементами *big.Int
//
// \sum_{i=1}^n \sum_{j=1}^n a_{ij} b_{ij}
func matscalar(A, B [][]*big.Int) *big.Int {
	N := len(A)
	sum := big.NewInt(0)
	tmp := new(big.Int)

	for i := 0; i < N; i++ {
		for j := 0; j < N; j++ {
			if A[i][j].Sign() == 0 || B[i][j].Sign() == 0 {
				continue
			}
			tmp.Mul(A[i][j], B[i][j])
			sum.Add(sum, tmp)
		}
	}

	return sum
}

// Извлекает i-e size бит из числа
func extractbits(a *big.Int, i int, size int) uint64 {
	shifted := new(big.Int).Rsh(a, uint(i*size))
	return shifted.Uint64() & (uint64(1)<<size - 1)
}

// Находит максимальный разрез
//
// Возвращает раскраску вершин графа G
func maxcut() []int8 {
	l = n + 1
	M = m * R

	coloring := make([]int8, n)
	for i := range n {
		coloring[i] = -1
	}

	W, _ := countcut(coloring)

	for i := range n {
		coloring[i] = 0
		Wi, _ := countcut(coloring)
		if Wi < W {
			coloring[i] = 1
		}
	}

	return coloring
}

// Находит максимальное количество переходных ребёр и сколько раз оно достигается
//
// На вход подаётся частичная раскраска вершин графа G
func countcut(coloring []int8) (int, uint64) {
	// Получим списки раскрашенных и нераскрашенных вершин

	uncolored := make([]int, 0, n)

	colored := make([]int, 0, n)

	for i, u := range coloring {
		if u < 0 {
			uncolored = append(uncolored, i)
		} else {
			colored = append(colored, i)
		}
	}

	N := len(uncolored)

	// Размер каждого разбиения нераскрашенных вершин графа
	var p int = N / 3

	// Разбиения нераскрашенных вершин графа
	I, J, K := make([]int, p), make([]int, p), make([]int, p)

	// Тривиальное распределение вершин для получения непересекающихся множеств
	for i := range p {
		I[i] = uncolored[i]
		J[i] = uncolored[p+i]
		K[i] = uncolored[2*p+i]
	}

	// Количество невошедших в разбиения вершин
	var a int = N - 3*p

	// Все вершины, для которых уже известны раскраски
	rest := make([]int, 0, len(colored)+a)

	// Кладём туда невошедшие в разбиения вершины, потому что бы потом будем перебирать для них раскраски
	for i := range a {
		rest = append(rest, uncolored[3*p+i])
	}

	// ...и уже раскрашенные вершины
	rest = append(rest, colored...)

	// Непосредственно переданная в функцию раскраска
	var xcolored uint64

	for i, u := range colored {
		xcolored |= uint64(coloring[u]) << i
	}

	// Для возможности подсчёта и удобства прикрепляем уже раскрашенные вершины к множеству K
	K = append(K, rest...)

	// Размер матриц
	q := 1 << p

	// Вспомогательная переменная для хранения суммарного веса выполненных ограничений при
	// конкретных присваиваниях (в нашем случае, переходных рёбер при конкретных раскрасках)
	var r int

	// Вспомогательная переменная для хранения \beta^r
	var betar *big.Int

	// Матрицу A заполним сразу, т.к. она не зависит от элементов из K
	A := make([][]*big.Int, q)
	for xI := range uint64(q) {
		A[xI] = make([]*big.Int, q)
		for xJ := range uint64(q) {
			r = w(xI, xI, I, I) + w(xI, xJ, I, J) + w(xJ, xJ, J, J)
			betar = new(big.Int)
			betar.SetBit(betar, l*r, 1)
			A[xI][xJ] = betar
		}
	}

	// Остальные матрицы просто инициализируем

	B := make([][]*big.Int, q)
	for i := range uint64(q) {
		B[i] = make([]*big.Int, q)
	}

	C := make([][]*big.Int, q)
	for i := range uint64(q) {
		C[i] = make([]*big.Int, q)
	}

	// Раскраска для уже раскрашенных вершин + невошедших в разбиения
	var xrest uint64

	// Максимальное количество переходных рёбер при переданной в функцию раскраске
	var W int

	// Сколько раз достигается W
	var alphaW uint64

	// Перебираем все раскаски невошедших в разбиения вершин
	for xa := range 1 << a {
		xrest = (xcolored << a) | uint64(xa)

		// Случай когда количество нераскрашенных вершин < 3
		//
		// Тогда множество K содержит все вершины графа и мы
		// счиатем для него количество переходных ребёр
		if p < 1 {
			r = w(xrest, xrest, K, K)
			if r > W {
				W = r
				alphaW = 1
			} else if r == W {
				alphaW += 1
			}
			continue
		}

		for xI := range uint64(q) {
			for k := range uint64(q) {
				xK := (xrest << p) | k
				r = w(xI, xK, I, K) + w(xK, xK, K, K)
				betar = new(big.Int)
				betar.SetBit(betar, l*r, 1)
				B[xI][k] = betar
			}
		}

		for xJ := range uint64(q) {
			for k := range uint64(q) {
				xK := (xrest << p) | k
				r = w(xJ, xK, J, K)
				betar = new(big.Int)
				betar.SetBit(betar, l*r, 1)
				C[xJ][k] = betar
			}
		}

		D := matmul(B, C, true)

		// Считаем именно сумму произведений соответствующих элементов
		gamma := matscalar(A, D)

		for r := M; r >= 0; r-- {
			alpha := extractbits(gamma, r, l)
			if alpha == 0 {
				continue
			}
			if r > W {
				W = r
				alphaW = alpha
				break
			}
			if r == W {
				alphaW += 1
				break
			}
		}
	}

	return W, alphaW
}

func main() {
	fmt.Scan(&n)

	G = make([][]bool, n)
	for i := range n {
		G[i] = make([]bool, n)
	}

	// На вход по очереди подаются две вершины (ребра)
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

	if n < 3 {
		fmt.Println("1")
		return
	}

	coloring := maxcut()

	// Часть, к которой принадлежит первая вершина (её цвет)
	color1 := coloring[0]

	// Вспомогательная переменная для вывода веришн
	first := true

	for i, color := range coloring {
		if color == color1 {
			if !first {
				fmt.Print(" ")
			}
			first = false
			fmt.Print(i + 1)
		}
	}
}
