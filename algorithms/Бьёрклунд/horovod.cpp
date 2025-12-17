// Хоровод. Задача о гамильтоновом цикле в двудольном графе. Алгоритм Бьёрклунда
// Соколовский Роман - 2025 г.

#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <cstdint>
#include <random>
using namespace std;

// n - количество вершин (2 <= n <= 50)
int n;

// G - двунаправленный двудольный граф
vector<vector<uint8_t>> G;

// s - специальная вершина
int s;

// k - степень конечного поля GF(2^k) (2 <= k <= 8)
int k;

// irredpolys - неприводимые полиномы над полем k-ой степени
// https://www.jjj.de/mathdata/all-irredpoly.txt
uint16_t irredpolys[7] = {
    0b111,       // 2,1,0
    0b1011,      // 3,1,0
    0b10011,     // 4,1,0
    0b100101,    // 5,2,0
    0b1000011,   // 6,1,0
    0b10000011,  // 7,1,0
    0b100011101  // 8,4,3,2,0
};

vector<uint8_t> pows_gf2;
vector<int> logs_gf2;

// Генерация таблиц для эффеткивного умножения и деления в GF(2^k)
// gently взято с хабра
void generate_gf2() {
    int power = 1 << k;
    pows_gf2.assign(power, 0);
    logs_gf2.assign(power, 0);

    pows_gf2[0] = 1;
    logs_gf2[0] = -1;
    logs_gf2[1] = 0;

    for (int i = 1; i < power - 1; i++) {
        uint16_t x = (uint16_t)pows_gf2[i - 1] << 1;
        if (x & (1 << k))
            x ^= irredpolys[k - 2];

        pows_gf2[i] = (uint8_t)x;
        logs_gf2[pows_gf2[i]] = i;
    }

    pows_gf2[power - 1] = 1;
}

// Умножение в GF(2^k)
uint8_t mul_gf(uint8_t a, uint8_t b) {
    if (a == 0 || b == 0)
        return 0;
    int r = logs_gf2[a] + logs_gf2[b];
    int mod = (int)pows_gf2.size() - 1;
    if (r >= mod) r -= mod;
    return pows_gf2[r];
}

// Деление в GF(2^k)
uint8_t div_gf(uint8_t a, uint8_t b) {
    if (b == 0) throw runtime_error("division by zero");
    if (a == 0) return 0;
    int r = logs_gf2[a] - logs_gf2[b];
    int mod = (int)pows_gf2.size() - 1;
    if (r < 0) r += mod;
    return pows_gf2[r];
}

// Рандомные числа в GF(2^k) за исключением чисел в neq
uint8_t rand_gf(initializer_list<uint8_t> neq = {}) {
    int shift = 1 << k;
    while (true) {
        uint8_t r = rand() % shift;
        bool skip = false;
        for (uint8_t x : neq)
            if (r == x) { skip = true; break; }
        if (!skip) return r;
    }
}

uint8_t permanent(const vector<vector<uint8_t>>& A) {
    int m = A.size();
    vector<vector<uint8_t>> B = A;

    for (int i = 0; i < m; i++) {
        if (B[i][i] == 0) {
            for (int j = i + 1; j < m; j++) {
                if (B[j][i] != 0) {
                    swap(B[i], B[j]);
                    break;
                }
            }
        }
        if (B[i][i] == 0)
            return 0;

        for (int j = i + 1; j < m; j++) {
            if (B[j][i] != 0) {
                uint8_t mval = div_gf(B[j][i], B[i][i]);
                for (int k = i; k < m; k++)
                    B[j][k] ^= mul_gf(mval, B[i][k]);
            }
        }
    }

    uint8_t perm = 1;
    for (int i = 0; i < m; i++)
        perm = mul_gf(perm, B[i][i]);
    return perm;
}

bool hamiltonicity_bipartite() {
    // Берем k из условия 2^k > c*n
    int c = 2;
    for (int i = 10; i > 0; i--) {
        if ((c * n) & (1 << i)) {
            k = i + 1;
            break;
        }
    }

    // Генерируем таблицы степеней и логарифмов для GF(2^k)
    // для эффективного умножения и деления
    generate_gf2();

    // Выбираем специальную вершину, принадлежащую V1
    s = 0;

    // Формируем множеcтва V1 и V2 по долям
    vector<int> V1(n / 2), V2(n / 2);
    for (int i = 0; i < n / 2; i++) {
        V1[i] = i;
        V2[i] = n / 2 + i;
    }

    // Формируем матрицу N
    vector<vector<uint32_t>> N(n / 2, vector<uint32_t>(n / 2, 0));

    // Считаем количество ребер между долями
    int transitions_amount = 0;

    for (int u = 0; u < n / 2; u++) {
        for (int v = 0; v < n / 2; v++) {
            if (u == v) continue;
            for (int w = 0; w < n / 2; w++) {
                if (G[u][w + n / 2] && G[v][w + n / 2]) {
                    transitions_amount++;
                    N[u][v] |= (1u << w);
                }
            }
        }
    }

    // Очевидно
    if (transitions_amount < n)
        return false;

    // Вводим переменные x_{u,v} для арок в G
    vector<vector<uint8_t>> VARS(n, vector<uint8_t>(n));

    // Инициализируем матрицу под перманентом
    vector<vector<uint8_t>> T(n / 2, vector<uint8_t>(n / 2));

    // Находим значение полинома в разных точках
    for (int iter = 0; iter < n / 2; iter++) {
        // LABELED CYCLE COVER SUM
        uint8_t lccs = 0;

        uint8_t r = 0;

        // Присваиваем случайные значения для переменных x_{u,v}
        for (int i = 0; i < n - 1; i++) {
            for (int j = n - 1; j > i; j--) {
                if (G[i][j]) {
                    r = rand_gf({0});
                    VARS[i][j] = r;
                    VARS[j][i] = r;
                }
            }
        }

        // Делаем так, чтобы x_{u,v} != x_{v,u} при u == s || v == sы
        for (int i = n - 1; i >= 0; i--) {
            if (VARS[i][s] == 0 || i == s) continue;
            if (i < s)
                VARS[s][i] = rand_gf({VARS[i][s], 0});
            else
                VARS[i][s] = rand_gf({VARS[s][i], 0});
        }

        uint32_t L_subsets_amount = 1u << V2.size();

        // Ищем все поднможества маркировок Y \subseteq L = V2
        for (uint32_t Y_mask = 1; Y_mask < L_subsets_amount; Y_mask++) {
            // Находим коффициенты для матрицы T
            for (int u = 0; u < n / 2; u++) {
                for (int v = 0; v < n / 2; v++) {
                    if (u == v) continue;
                    uint32_t Z_mask = N[u][v] & Y_mask;
                    for (int i = 0; i < n / 2; i++) {
                        if (Z_mask & (1u << i))
                            T[u][v] ^= mul_gf(VARS[u][i + n / 2], VARS[i + n / 2][v]);
                    }
                }
            }
            lccs ^= permanent(T);
        }

        if (lccs > 0)
            return true;
    }

    return false;
}

int main() {
    // K - количество ребёр
    int K;
    cin >> n >> K;

    G.assign(n, vector<uint8_t>(n, 0));

    // U1, U2 - множества вершин в графе
    vector<string> U1(n / 2), U2(n / 2);
    string a, b;
    int p = 0, q = 0;

    for (int i = 0; i < K; i++) {
        cin >> a >> b;

        for (int i1 = 0; i1 < n / 2; i1++) {
            if (U1[i1].empty() || U1[i1] == a) {
                if (U1[i1].empty())
                    U1[i1] = a;
                p = i1;
                break;
            }
        }

        for (int j1 = 0; j1 < n / 2; j1++) {
            if (U2[j1].empty() || U2[j1] == b) {
                if (U2[j1].empty())
                    U2[j1] = b;
                q = j1;
                break;
            }
        }

        G[p][q + n / 2] = 1;
        G[q + n / 2][p] = 1;
    }

    bool yes = hamiltonicity_bipartite();
    cout << (yes ? "yes" : "no") << endl;
}
