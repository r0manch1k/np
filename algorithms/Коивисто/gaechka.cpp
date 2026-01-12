// Гаечка. Задача о максимальном разрезе в графе. Алгоритм Коивисто

#include <iostream>
#include <vector>
#include <cstdint>
#include <utility>
#include <algorithm>
#include <boost/multiprecision/cpp_int.hpp>
#include <string>
#include <sstream>
#include <limits>

using namespace std;
using boost::multiprecision::cpp_int;

// n - количество вершин
int n;

// m - количество ребёр
int m;

// G - исходный граф
vector<vector<bool>> G;

// Максимальный вес ограничения (в нашем случае, ребро либо переходое, либо нет)
int R = 1;

// Максимальный суммарный вес ограничений (в нашем случае, сколько рёбер может быть переходными)
int M;

// Количество бит, достаточное для кодирования количества выполненных ограничений (в нашем случае, переходных ребёр)
int l;

// Возвращает количество переходных ребёр между вершинами I и J
// при их раскрасках xI и xJ соответственно
int w(uint64_t xI, uint64_t xJ, const vector<int>& I, const vector<int>& J) {
	int transitions = 0;

	// Если множества вершин I и J равны, то необходимо поделить
	// результат пополам из-за специфики реализации
	bool ii = false;

	for (size_t i = 0; i < I.size(); i++) {
		for (size_t j = 0; j < J.size(); j++) {
			int u = I[i];
			int v = J[j];
			if (!ii && u == v) {
				ii = true;
			}
			if (G[u][v] && (((xI >> i) & 1) != ((xJ >> j) & 1))) {
				transitions += 1;
			}
		}
	}

	if (ii && transitions > 0) {
		transitions /= 2;
	}

	return transitions;
}

// Умножает две матрицы с элементами *big.Int
//
// Если параметр T=true, то вычисляется A x B^T
vector<vector<cpp_int>> matmul(
	const vector<vector<cpp_int>>& A,
	const vector<vector<cpp_int>>& B,
	bool T
) {
	int N = A.size();

	vector<vector<cpp_int>> D(N, vector<cpp_int>(N));

	cpp_int tmp;

	for (int i = 0; i < N; i++) {
		for (int k = 0; k < N; k++) {
			if (A[i][k] == 0) continue;

			for (int j = 0; j < N; j++) {
				const cpp_int& bkj = T ? B[j][k] : B[k][j];
				if (bkj == 0) continue;

				tmp = A[i][k] * bkj;
				D[i][j] += tmp;
			}
		}
	}

	return D;
}

// Вычисляет скалярное произведение матриц с элементами *big.Int
//
// \sum_{i=1}^n \sum_{j=1}^n a_{ij} b_{ij}
cpp_int matscalar(
	const vector<vector<cpp_int>>& A,
	const vector<vector<cpp_int>>& B
) {
	int N = A.size();
	cpp_int sum = 0;
	cpp_int tmp;

	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			if (A[i][j] == 0 || B[i][j] == 0) continue;
			tmp = A[i][j] * B[i][j];
			sum += tmp;
		}
	}

	return sum;
}

// Извлекает i-e size бит из числа
uint64_t extractbits(const cpp_int& a, int i, int size) {
	cpp_int shifted = a >> (i * size);
	uint64_t mask = (uint64_t(1) << size) - 1;
	return (uint64_t)(shifted & mask);
}

// Находит максимальный разрез
//
// Возвращает раскраску вершин графа G
vector<int8_t> maxcut();

// Находит максимальное количество переходных ребёр и сколько раз оно достигается
//
// На вход подаётся частичная раскраска вершин графа G
pair<int, uint64_t> countcut(const vector<int8_t>& coloring);

vector<int8_t> maxcut() {
	l = n + 1;
	M = m * R;

	vector<int8_t> coloring(n, -1);

	auto res = countcut(coloring);
	int W = res.first;

	for (int i = 0; i < n; i++) {
		coloring[i] = 0;
		int Wi = countcut(coloring).first;
		if (Wi < W) {
			coloring[i] = 1;
		}
	}

	return coloring;
}

pair<int, uint64_t> countcut(const vector<int8_t>& coloring) {
	// Получим списки раскрашенных и нераскрашенных вершин

	vector<int> uncolored;
	vector<int> colored;

	for (int i = 0; i < n; i++) {
		if (coloring[i] < 0) {
			uncolored.push_back(i);
		} else {
			colored.push_back(i);
		}
	}

	int N = uncolored.size();

	// Размер каждого разбиения нераскрашенных вершин графа
	int p = N / 3;

	// Разбиения нераскрашенных вершин графа
	vector<int> I(p), J(p), K(p);

	for (int i = 0; i < p; i++) {
		I[i] = uncolored[i];
		J[i] = uncolored[p + i];
		K[i] = uncolored[2 * p + i];
	}

	// Количество невошедших в разбиения вершин
	int a = N - 3 * p;

	vector<int> rest;

	for (int i = 0; i < a; i++) {
		rest.push_back(uncolored[3 * p + i]);
	}

	rest.insert(rest.end(), colored.begin(), colored.end());

	uint64_t xcolored = 0;
	for (size_t i = 0; i < colored.size(); i++) {
		xcolored |= uint64_t(coloring[colored[i]]) << i;
	}

	K.insert(K.end(), rest.begin(), rest.end());

	int q = 1 << p;

	int r;
	cpp_int betar;

	vector<vector<cpp_int>> A(q, vector<cpp_int>(q));

	for (uint64_t xI = 0; xI < (uint64_t)q; xI++) {
		for (uint64_t xJ = 0; xJ < (uint64_t)q; xJ++) {
			r = w(xI, xI, I, I)
			  + w(xI, xJ, I, J)
			  + w(xJ, xJ, J, J);
			betar = cpp_int(1) << (l * r);
			A[xI][xJ] = betar;
		}
	}

	vector<vector<cpp_int>> B(q, vector<cpp_int>(q));
	vector<vector<cpp_int>> C(q, vector<cpp_int>(q));

	uint64_t xrest = 0;
	int W = 0;
	uint64_t alphaW = 0;

	for (uint64_t xa = 0; xa < (uint64_t)(1 << a); xa++) {
		xrest = (xcolored << a) | xa;

		if (p < 1) {
			r = w(xrest, xrest, K, K);
			if (r > W) {
				W = r;
				alphaW = 1;
			} else if (r == W) {
				alphaW++;
			}
			continue;
		}

		for (uint64_t xI = 0; xI < (uint64_t)q; xI++) {
			for (uint64_t k = 0; k < (uint64_t)q; k++) {
				uint64_t xK = (xrest << p) | k;
				r = w(xI, xK, I, K) + w(xK, xK, K, K);
				B[xI][k] = cpp_int(1) << (l * r);
			}
		}

		for (uint64_t xJ = 0; xJ < (uint64_t)q; xJ++) {
			for (uint64_t k = 0; k < (uint64_t)q; k++) {
				uint64_t xK = (xrest << p) | k;
				r = w(xJ, xK, J, K);
				C[xJ][k] = cpp_int(1) << (l * r);
			}
		}

		auto D = matmul(B, C, true);
		cpp_int gamma = matscalar(A, D);

		for (r = M; r >= 0; r--) {
			uint64_t alpha = extractbits(gamma, r, l);
			if (alpha == 0) continue;

			if (r > W) {
				W = r;
				alphaW = alpha;
				break;
			}
			if (r == W) {
				alphaW += alpha;
				break;
			}
		}
	}

	return {W, alphaW};
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    cin >> n;
    cin.ignore(numeric_limits<streamsize>::max(), '\n');

    G.assign(n, vector<bool>(n, false));

    int u, v;
    string line;

    // Читаем рёбра до пустой строки или EOF (поведение как у fmt.Scanln в Go)
    while (true) {
        if (!getline(cin, line)) {
            // EOF
            break;
        }
        if (line.empty()) {
            // пустая строка
            break;
        }

        stringstream ss(line);
        if (!(ss >> u >> v)) {
            break;
        }

        G[u - 1][v - 1] = true;
        G[v - 1][u - 1] = true;
        m += 1;
    }

    if (n < 3) {
        cout << "1\n";
        return 0;
    }

    auto coloring = maxcut();

    // Часть, к которой принадлежит первая вершина (её цвет)
    int color1 = coloring[0];

    // Вспомогательная переменная для вывода вершин
    bool first = true;

    for (int i = 0; i < n; i++) {
        if (coloring[i] == color1) {
            if (!first) cout << " ";
            first = false;
            cout << i + 1;
        }
    }
    cout << "\n";
}