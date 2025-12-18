#include <iostream>
#include <vector>
#include <cstdint>
#include <string>
#include <sstream>
#include <limits>

using namespace std;

// n - количество вершин (округлённое вверх для кратности трём)
int n;

// m - количество рёбер
int m = 0;

// G - исходный граф (с возможно доп. кол-вом вершин для кратности n трём)
vector<vector<bool>> G;

/*
 * Считает количество выполненных ограничений при присваиваниях Li и Lj
 *
 * В нашем случае: считает количество переходных рёбер при данных
 * раскрасках Li и Lj в подмножествах Vi и Vj графа G
 *
 * Параметры i и j нужны для определения подмножества вершин в
 * графе G (т.к. мы просто разбили их, поставив две "перегородки",
 * то достаточно индекса)
 *
 * P.S. Работает примерно за Θ(n^2/9), если не считать сдвиги.
 * Пока что-то быстрее не придумал
 * Еще можно прикрутить кэширование
 */
uint8_t w(int Li, int Lj, int i, int j) {
    uint8_t transitions = 0;

    // Вспомогательные переменные для оптимизации подсчёта
    int pshift, qshift;

    // Количество вершин в подмножестве G
    int K = n / 3;

    for (int p = i * K; p < (i + 1) * K; ++p) {
        pshift = p - i * K;
        for (int q = j * K; q < (j + 1) * K; ++q) {
            qshift = q - j * K;
            if (G[p][q] &&
                (((1 << pshift) & Li) > 0) != (((1 << qshift) & Lj) > 0)) {
                transitions += 1;
            }
        }
    }

    if (i == j) {
        transitions /= 2;
    }

    return transitions;
}

/*
 * Ищет первый попавшийся треугольник в булевой матрице A
 * Возвращает отсортированный массив индексов вершин из разных долей
 */
vector<int> triangle(const vector<vector<bool>>& A) {
    int N = (int)A.size();

    for (int i = 0; i < N; ++i) {
        for (int j = i + 1; j < N; ++j) {
            if (!A[i][j]) {
                continue;
            }
            for (int k = j + 1; k < N; ++k) {
                if (A[i][k] && A[j][k]) {
                    return {i, j, k};
                }
            }
        }
    }
    return {};
}

/*
 * Находит максимальный разрез,
 * возвращая три маски для каждого подмножества вершин из G
 */
vector<int> maxcut() {
    // Суммарное количество вершин (присваиваний/раскрасок) в долях графа H
    int K = 3 * (1 << (n / 3));

    // Трёхдольный граф H
    vector<vector<uint8_t>> H(K, vector<uint8_t>(K));

    // Размер доли в H
    int H_part_size = 1 << (n / 3);

    // Вспомогательные переменные для хранения индексов
    int a, b;

    // Находим веса H вариантом из статьи
    for (int j = 0; j < 3; ++j) {
        for (int l = j + 1; l < 3; ++l) {
            for (int Lj = 0; Lj < H_part_size; ++Lj) {
                a = j * H_part_size + Lj;
                for (int Ll = 0; Ll < H_part_size; ++Ll) {
                    b = l * H_part_size + Ll;
                    if (j > 0) {
                        H[a][b] = w(Lj, Ll, j, l);                // i23
                    } else if (j == 0 && l > 1) {
                        H[a][b] = w(Ll, Ll, l, l) + w(Lj, Ll, j, l); // i12
                    } else {
                        H[a][b] = w(Lj, Lj, j, j)
                                + w(Ll, Ll, l, l)
                                + w(Lj, Ll, j, l);                // i13
                    }
                    H[b][a] = H[a][b];
                }
            }
        }
    }

    // Булевая матрица смежности для H при i12, i13 и i23
    vector<vector<bool>> Hi(K, vector<bool>(K));

    // Здесь можно улучшить, по-умному перебирая решения
    // i12 + i13 + i23 = N, N ∈ [0, m]
    for (int N = m; N >= 0; --N) {
        for (int i12 = m; i12 >= 0; --i12) {
            for (int i13 = m; i13 >= 0; --i13) {
                for (int i23 = m; i23 >= 0; --i23) {
                    if (i12 + i13 + i23 != N) {
                        continue;
                    }

                    // Заполняем матрицу с конкретными i12, i13 и i23
                    for (int j = 0; j < 3; ++j) {
                        for (int l = j + 1; l < 3; ++l) {
                            for (int Lj = 0; Lj < H_part_size; ++Lj) {
                                a = j * H_part_size + Lj;
                                for (int Ll = 0; Ll < H_part_size; ++Ll) {
                                    b = l * H_part_size + Ll;
                                    if (j > 0) {
                                        Hi[a][b] = (H[a][b] == (uint8_t)i23);
                                    } else if (j == 0 && l > 1) {
                                        Hi[a][b] = (H[a][b] == (uint8_t)i13);
                                    } else {
                                        Hi[a][b] = (H[a][b] == (uint8_t)i12);
                                    }
                                    Hi[b][a] = Hi[a][b];
                                }
                            }
                        }
                    }

                    // Можно не заполнять матрицу, а при нахождении треугольника вычислять значения ячеек

                    auto tr = triangle(Hi);
                    if (!tr.empty()) {
                        return tr;
                    }
                }
            }
        }
    }

    return {};
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    // Исходное количество вершин
    int K;
    cin >> K;
    cin.ignore(numeric_limits<streamsize>::max(), '\n');

    // Делаем количество вершин кратным трём
    n = ((K + 2) / 3) * 3;

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

    if (K < 3) {
        cout << "1\n";
        return 0;
    }

    vector<int> partition = maxcut();

    // Часть, к которой принадлежит первая вершина (её цвет)
    int color1 = partition[0] & 1;

    // Вспомогательная переменная для вывода вершин
    bool first = true;

    for (int i = 0; i < (int)partition.size(); ++i) {
        int mask = partition[i];
        for (int j = 0; j < n / 3; ++j) {
            if (((mask >> j) & 1) == color1) {
                if (!first) {
                    cout << " ";
                }
                first = false;
                cout << i * (n / 3) + j + 1;
            }
        }
    }
    return 0;
}
