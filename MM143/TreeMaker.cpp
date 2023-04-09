// clang-format off
#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>

#define mp make_pair
#define fst first
#define snd second
#define forn(i,n) for (int i = 0; i < int(n); i++)
#define forn1(i,n) for (int i = 1; i <= int(n); i++)
#define popcnt __builtin_popcountll
#define ffs __builtin_ffsll
#define ctz __builtin_ctzll
#define clz __builtin_clz
#define clzll __builtin_clzll
#define all(a) (a).begin(), (a).end()

using namespace std;
using namespace __gnu_pbds;

using uint = unsigned int;
using ll = long long;
using ull = unsigned long long;
using pii = pair<int,int>;
using pli = pair<ll,int>;
using pil = pair<int,ll>;
using pll = pair<ll,ll>;
template <typename T> using vec = vector<T>;
using vi = vec<int>;
using vl = vec<ll>;
template <typename T> using que = queue<T>;
template <typename T> using deq = deque<T>;
template <typename T> using ordered_set = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
template <typename K, typename V> using ordered_map = tree<K, V, less<K>, rb_tree_tag, tree_order_statistics_node_update>;

template <typename T> T id(T b) {return b;};
template <typename T> void chmax(T &x, T y) {if (x < y) x = y;}
template <typename T> void chmin(T &x, T y) {if (x > y) x = y;}
template <typename S, typename K> bool contains(S &s, K k) { return s.find(k) != s.end(); }
template <typename T> bool testb(T flag, size_t i) { return (flag>>i) & 1; }
template <typename T> T setb(T flag, size_t i) { return flag | (T(1)<<i); }
template <typename T> T clearb(T flag, size_t i) { return flag & ~(T(1)<<i); }
void fastio() { ios_base::sync_with_stdio(false); cin.tie(nullptr); }
constexpr ll TEN(int n) { return n == 0 ? 1LL : 10LL*TEN(n-1); }
// clang-format on

using Rng = mt19937_64;
Rng rng(7241567);

template <typename T>
inline typename enable_if<is_integral<T>::value, T>::type rand_range(T l, T r) {
    assert(l < r);
    return uniform_int_distribution<T>(l, r - 1)(rng);
}

template <typename T>
inline typename enable_if<is_floating_point<T>::value, T>::type rand_range(T l, T r) {
    assert(l < r);
    return uniform_real_distribution<double>(l, r)(rng);
}

inline bool rand_bool(double p) {
    assert(0.0 <= p and p <= 1.0);
    static auto dist = uniform_real_distribution<double>(0.0, nextafter(1.0, DBL_MAX));
    return dist(rng) <= p;
}

using Clock = chrono::high_resolution_clock;
using Duration = Clock::duration;
class Stopwatch {
private:
    chrono::time_point<Clock> begin;
    chrono::time_point<Clock> prev;

public:
    Stopwatch() {
        begin = Clock::now();
        prev = begin;
    }

    static Stopwatch start() {
        return Stopwatch();
    }

    Duration elapsed() const {
        return Clock::now() - begin;
    }

    Duration lap() {
        auto temp = prev;
        prev = Clock::now();
        return prev - temp;
    }
};

inline ll as_millis(const Duration& dur) {
    return chrono::duration_cast<chrono::milliseconds>(dur).count();
}

inline ll as_micros(const Duration& dur) {
    return chrono::duration_cast<chrono::microseconds>(dur).count();
}

inline constexpr Duration from_millis(ll millis) {
    return chrono::milliseconds(millis);
}

inline constexpr Duration from_micros(ll micros) {
    return chrono::milliseconds(micros);
}

struct Scheduler {
    double t0, t1;
    Duration time_limit;
    Stopwatch instant;
    Scheduler(double t0, double t1, Duration time_limit)
        : t0(t0), t1(t1), time_limit(time_limit), instant(Stopwatch::start()) {
    }

    double temperature() const {
        double progression = double(as_micros(instant.elapsed())) / double(as_micros(time_limit));
        return pow(t0, 1.0 - progression) * pow(t1, progression);
    }

    bool is_timeout() const {
        return instant.elapsed() > time_limit;
    }
};

template <typename T>
double transition_probability_max(T old_score, T new_score, double temperature) {
    double delta = new_score - old_score;
    return delta > 0.0 ? 1.0 : exp(delta / temperature);
}

template <typename T>
double transition_probability_min(T old_score, T new_score, double temperature) {
    double delta = old_score - new_score;
    return delta > 0.0 ? 1.0 : exp(delta / temperature);
}

const int DI[4] = { -1, 0, 1, 0 };
const int DJ[4] = { 0, 1, 0, -1 };
const string DIR = "URDL";
using Dir = unsigned char;
const Dir U = 0, R = 1, D = 2, L = 3;

template <typename T>
void swap_remove(vector<T>& l, const int i) {
    const int j = l.size() - 1;
    if (i != j) {
        swap(l[i], l[j]);
    }
    l.pop_back();
}

const Duration TL = from_millis(9500);

vec<vi> perm4;

// 7ビットのうち下位4ビット(0..15)をタイルの種類,上位3ビット(1..4)を色とする
// 0なら空
using Cell = unsigned char;
using Grid = vector<vector<Cell>>;
inline Cell make_cell(char tile, char color) {
    return tile | (color << 4);
}
inline Cell clear_tile(Cell cell) {
    return cell & (((1 << 3) - 1) << 4);
}
inline Cell clear_color(Cell cell) {
    return cell & ((1 << 4) - 1);
}
inline Cell set_tile(Cell cell, char tile) {
    return clear_tile(cell) | tile;
}
inline Cell set_color(Cell cell, char color) {
    return clear_color(cell) | (color << 4);
}
inline char get_tile(Cell cell) {
    return clear_color(cell);
}
inline char get_color(Cell cell) {
    return clear_tile(cell) >> 4;
}
inline bool is_empty_cell(Cell cell) {
    return cell == 0;
}
inline Cell extend_pipe(Cell cell, int dir) {
    return make_cell(setb(get_tile(cell), dir), get_color(cell));
}
inline Cell shrink_pipe(Cell cell, int dir) {
    return make_cell(clearb(get_tile(cell), dir), get_color(cell));
}
inline bool has_pipe(Cell cell, int dir) {
    return testb(get_tile(cell), dir);
}

inline int opposite(int dir) {
    return (dir + 2) & ((1 << 2) - 1);
}
inline bool is_leaf(Cell cell) {
    return popcnt(get_tile(cell)) == 1;
}

using Solution = vec<pii>;

struct Solver {
    int n, c, p;
    Grid grid;
    Cell extra;
    // 各種セルの個数
    vi count;
    Stopwatch sw;

    Solver() {
        cin >> n >> c >> p;
        grid = vec<vec<Cell>>(n, vec<Cell>(n));

        forn(i, n) forn(j, n) {
            int tile, color;
            cin >> tile >> color;
            color++;
            grid[i][j] = make_cell(tile, color);
        }

        int etile, ecolor;
        cin >> etile >> ecolor;
        ecolor++;
        extra = make_cell(etile, ecolor);

        count = count_tile(grid);
        count[extra]++;

        sw = Stopwatch::start();
    }

    void solve() {
        const int initial_score = grid_score(grid);

        sw.lap();

        Grid base = random_target();
        int diff = diff_cells(base);
        forn(k, 100) {
            Grid temp_target = random_target();
            int temp_diff = diff_cells(base);
            if (temp_diff < diff) {
                diff = temp_diff;
                base = temp_target;
            }
        }

        fprintf(stderr, "inital forest: lap = %lldms\n", as_millis(sw.lap()));

        auto target = find_target(base, from_millis(5000));

        fprintf(stderr, "target forest: lap = %lldms\n", as_millis(sw.lap()));

        target = actual_target(target);

        auto actual_count = count_tile(target);
        int s = 0;
        forn(i, actual_count.size()) {
            s += abs(count[i] - actual_count[i]);
        }
        assert(s == 1);

        auto solution = beam_search(grid, extra, target);
        // auto solution = greedy(grid, extra, target);

        fprintf(stderr, "solution generation: lap = %lldms\n", as_millis(sw.lap()));

        fprintf(stderr, "before output: %lldms\n", as_millis(sw.elapsed()));

        cout << solution.size() << "\n";
        for (auto [d, i] : solution) {
            cout << DIR[d] << " " << i << "\n";
            // cerr << DIR[d] << " " << i << endl;
        }

        const int final_score = grid_score(grid) + solution.size();

        fprintf(stderr, "score: %d -> %d (gen:%d)\n", initial_score, final_score, 2 * n * n + c);
    }

    Solution random_solution(int m) {
        assert(0 <= m and m <= 10000);
        vec<pii> sol;
        forn(i, m) {
            int dir = rand_range(0, 4);
            int x = rand_range(0, n);
            sol.emplace_back(dir, x);
        }
        return sol;
    }

    Grid actual_target(const Grid& grid) {
        auto temp = count;

        vec<vec<Cell>> actual = vec<vec<Cell>>(n, vec<Cell>(n));

        vec<pii> not_assigned;
        // 左上から割り当てていく
        forn(i, n) forn(j, n) {
            if (temp[grid[i][j]] > 0) {
                actual[i][j] = grid[i][j];
                temp[grid[i][j]]--;
            } else {
                not_assigned.emplace_back(i, j);
            }
        }

        vec<Cell> rest;
        forn(cell, temp.size()) {
            forn(k, temp[cell]) {
                rest.push_back(cell);
            }
        }

        assert(rest.size() == not_assigned.size() + 1);

        for (auto [i, j] : not_assigned) {
            actual[i][j] = rest.back();
            rest.pop_back();
        }

        // not_assignedの中で入れ替えて適切な割当を探索
        const int m = not_assigned.size();
        fprintf(stderr, "not assigned: %d\n", m);
        if (m >= 2) {
            auto timer = Stopwatch::start();
            auto score = grid_score(actual);
            auto old = score;
            while (timer.elapsed() < from_millis(100)) {
                const auto i = rand_range(0, m - 1);
                const auto j = rand_range(i + 1, m);
                const auto [si, sj] = not_assigned[i];
                const auto [ti, tj] = not_assigned[j];
                swap(actual[si][sj], actual[ti][tj]);

                auto new_score = grid_score(actual);
                if (new_score <= score) {
                    score = new_score;
                } else {
                    swap(actual[si][sj], actual[ti][tj]);
                }
            }

            fprintf(stderr, "assignment optimization: %d -> %d\n", old, score);
        }

        return actual;
    }

    using State = tuple<int, int, Grid, Cell>;

    // greedyの候補選択の部分をバリエーションとしてビームサーチ化したもの
    Solution beam_search(Grid& grid, const Cell extra, const Grid& target) {
        vec<vec<Move>> sols = { vec<Move>() };
        vi par = { -1 };

        int insertion = 0;

        vec<priority_queue<State, vec<State>, greater<State>>> q(n * n);
        q[0].push({ 0, 0, grid, extra });
        insertion++;

        int best_score = TEN(6);
        int best_si = -1;

        while (sw.elapsed() < from_millis(9000)) {
            forn(row, n - 1) {
                forn(col, n) {
                    if (q[row * n + col].empty()) {
                        continue;
                    }

                    auto [total_len, par_i, grid, extra] = q[row * n + col].top();
                    q[row * n + col].pop();
                    auto moves = next_move(grid, extra, row, col, target);

                    for (auto move : moves) {
                        Grid new_grid = grid;
                        Cell new_extra = extra;
                        const int new_len = total_len + move.snd;

                        for (auto [dir, target_row, count] : move.fst) {
                            if (dir == L) {
                                new_extra = rotate_left(new_grid, new_extra, target_row - row, count);
                            } else if (dir == R) {
                                new_extra = rotate_right(new_grid, new_extra, target_row - row, count);
                            } else {
                                assert(false);
                            }
                        }

                        if (col == n - 1) {
                            // これより前の行は不要なので削除
                            new_grid.erase(new_grid.begin());
                        }

                        q[row * n + col + 1].emplace(new_len, sols.size(), new_grid, new_extra);
                        insertion++;

                        sols.push_back(move.fst);
                        par.push_back(par_i);
                    }
                }
            }

            if (q[n * (n - 1)].empty()) {
                continue;
            }

            // n-1行目の回転を全部試す
            auto [score, si, g, extra] = q[n * (n - 1)].top();
            q[n * (n - 1)].pop();
            // 左回転
            for (int ld = 0; ld <= n / 2 + 1; ld++) {
                auto temp_g = target;
                temp_g[n - 1] = g[0];
                rotate_left(temp_g, extra, 0, ld);
                int new_score = score + ld + grid_score(temp_g);
                if (new_score < best_score) {
                    best_score = new_score;
                    grid = temp_g;
                    best_si = sols.size();
                    sols.push_back({ { L, n - 1, ld } });
                    par.push_back(si);
                }
            }
            // 右回転
            for (int rd = 1; rd <= n / 2 + 1; rd++) {
                auto temp_g = target;
                temp_g[n - 1] = g[0];
                rotate_right(temp_g, extra, 0, rd);
                int new_score = score + rd + grid_score(temp_g);
                if (new_score < best_score) {
                    best_score = new_score;
                    grid = temp_g;
                    best_si = sols.size();
                    sols.push_back({ { R, n - 1, rd } });
                    par.push_back(si);
                }
            }
        }

        vec<pii> best_sol;
        vi idx;
        while (best_si != -1) {
            idx.push_back(best_si);
            best_si = par[best_si];
        }
        while (not idx.empty()) {
            auto i = idx.back();
            idx.pop_back();
            for (auto [dir, row, count] : sols[i]) {
                forn(x, count) best_sol.emplace_back(dir, row);
            }
        }

        fprintf(stderr, "insertion: %d\n", insertion);

        return best_sol;
    }

    using Move = tuple<Dir, int, int>;

    // gridが(n-i)*nであることに注意(相変わらずtargetはn*nであることも注意)
    vec<pair<vec<Move>, int>> next_move(const Grid& grid, const Cell extra, const int i, const int j, const Grid& target) {
        assert(i < n - 1);
        vec<pair<vec<Move>, int>> res;
        const auto target_cell = target[i][j];

        if (target_cell == extra) {
            vec<Move> sol = { { L, i, 1 } };
            res.emplace_back(sol, 1);
        }

        vec<pii> candidate;

        // 同じ行から
        for (int c = 0; c < n - j; c++) {
            if (grid[0][c] == target_cell) {
                candidate.emplace_back(0, c);
            }
        }

        // 次行以降
        for (int dr = 1; dr < grid.size(); dr++) {
            for (int c = 0; c < n; c++) {
                if (grid[dr][c] == target_cell) {
                    candidate.emplace_back(dr, c);
                }
            }
        }

        for (auto [di, tj] : candidate) {
            const int ti = i + di;
            vec<Move> moves;
            if (ti != i) {
                int ld = tj + 1;
                int rd = n - tj;
                if (ld <= rd) {
                    moves.emplace_back(L, ti, ld);
                } else {
                    moves.emplace_back(R, ti, rd);
                }

                moves.emplace_back(L, i, 1);
                res.emplace_back(moves, min(ld, rd) + 1);
            } else {
                assert(ti == i);

                if (j == 0) {
                    // (i,0)が目標位置であるセルに関しては単に右端へ動かすだけで良い
                    // ldの+1は最後に(R,i)する分
                    int ld = tj + 2;
                    int rd = n - tj - 1;

                    if (ld <= rd) {
                        moves.emplace_back(L, i, ld);
                    } else {
                        moves.emplace_back(R, i, rd);
                    }

                    res.emplace_back(moves, min(ld, rd));
                } else {
                    int ld = tj + 1;
                    // i(=ti)行目から目標セルを取り出す
                    moves.emplace_back(L, ti, ld);

                    // i+1行目の右端にtarget_cellを置く
                    moves.emplace_back(L, ti + 1, 1);

                    // i行目を元に戻す
                    moves.emplace_back(R, ti, ld);

                    // target_cellをi+1行目から取り出す
                    moves.emplace_back(R, ti + 1, 1);

                    // target_cellをi行目の右端に置く
                    moves.emplace_back(L, ti, 1);

                    res.emplace_back(moves, 2 * ld + 3);
                }
            }
        }

        return res;
    }

    // 左上に設置するセルから順に処理していく(その行の右端から詰めていく)
    // 候補となるセルのうち操作数が少ないものを貪欲に選ぶ
    // Solution greedy(Grid& grid, Cell extra, const Grid& target) {
    //     vec<pii> sol;
    //     forn(i, n - 1) forn(j, n) {
    //         auto res = next_move(grid, extra, i, j, target, 1);

    //         auto [s, new_grid, new_extra] = res[0];
    //         extra = new_extra;
    //         grid = new_grid;
    //         auto cnt = count_tile(grid);
    //         cnt[extra]++;

    //         assert(cnt == count);
    //         sol.insert(sol.end(), all(s));
    //     }

    //     return sol;
    // }

    // i行目をdだけ左回転し,その時の余分セルを返す.
    Cell rotate_left(Grid& grid, Cell extra, int i, int d) {
        assert(0 <= d and d <= n);
        if (d == 0) return extra;
        vec<Cell> new_row(n);
        Cell new_extra = grid[i][d - 1];
        copy(grid[i].begin() + d, grid[i].end(), new_row.begin());
        new_row[n - d] = extra;
        copy(grid[i].begin(), grid[i].begin() + d - 1, new_row.begin() + n - d + 1);
        swap(grid[i], new_row);
        return new_extra;
    }
    // i行目をdだけ右回転し,その時の余分セルを返す.
    Cell rotate_right(Grid& grid, Cell extra, int i, int d) {
        assert(0 <= d and d <= n);
        if (d == 0) return extra;
        vec<Cell> new_row(n);
        Cell new_extra = grid[i][n - d];
        copy(grid[i].begin(), grid[i].end() - d, new_row.begin() + d);
        new_row[d - 1] = extra;
        copy(grid[i].end() - d + 1, grid[i].end(), new_row.begin());
        swap(grid[i], new_row);
        return new_extra;
    }

    vi count_tile(const Grid& grid) {
        vi count((c << 4) + 15 + 1);
        forn(i, n) forn(j, n) {
            count[grid[i][j]]++;
        }
        return count;
    }

    bool in_grid(int i, int j) {
        return 0 <= i and i < n && 0 <= j and j < n;
    }

    bool is_extendable_cell(const Grid& grid, const int i, const int j) {
        if (is_empty_cell(grid[i][j])) return false;
        forn(dir, 4) {
            int ni = i + DI[dir], nj = j + DJ[dir];
            if (not in_grid(ni, nj)) continue;
            if (is_empty_cell(grid[ni][nj])) return true;
        }
        return false;
    }

    // 完成図を探索.
    // 適当なc個の連結成分からなる森から始めて,次の手順で各種セル(タイル,色)の個数が一致する方向へ山登り(焼きなまし).
    // 近傍は以下の2つ
    // 1.閉路を作ったあとその閉路の適当な辺を一つ除去
    // 2.葉ノードを異なる連結成分に移動
    Grid find_target(Duration time_limit) {
        return find_target(random_target(), time_limit);
    }

    Grid find_target(Grid grid, Duration time_limit) {
        auto timer = Stopwatch::start();
        vi target_count = count;

        auto count = count_tile(grid);

        // スコアは各セルの個数の差の和
        int score = 0;
        forn(i, count.size()) {
            score += abs(target_count[i] - count[i]);
        }

        auto initial_diff = score;
        auto best_score = score;
        auto best_target = grid;

        // fprintf(stderr, "initial diff score: %d\n", score);

        const auto scheduler = Scheduler(n * n, 1e-2, time_limit - timer.elapsed());
        double temperature = scheduler.temperature();

        int step = 0;
        int transition_count = 0;
        while (true) {
            if (step % 100 == 0) {
                if (scheduler.is_timeout()) {
                    break;
                }
                temperature = scheduler.temperature();
            }
            step++;

            // メインセルの選択
            const int i = rand_range(0, n);
            const int j = rand_range(0, n);
            auto& cell = grid[i][j];

            // 隣接セルの選択
            const int dir = rand_range(0, 4);
            if (has_pipe(cell, dir)) continue;

            const int ni = i + DI[dir], nj = j + DJ[dir];
            if (not in_grid(ni, nj)) continue;
            auto& ncell = grid[ni][nj];

            if (not(is_leaf(cell) or (get_color(cell) == get_color(ncell)))) {
                continue;
            }

            map<pii, Cell> old_cells;
            auto snapshot = [&](int i, int j) {
                // "元"のデータのみを保存する
                if (old_cells.count({ i, j }) == 0) {
                    old_cells[{ i, j }] = grid[i][j];
                }
            };
            map<pii, Cell> new_cells;
            auto add_new_cell = [&](int i, int j, Cell cell) {
                new_cells[{ i, j }] = cell;
            };

            snapshot(i, j);
            snapshot(ni, nj);

            // 近傍1
            if (get_color(cell) == get_color(ncell)) {
                cell = extend_pipe(cell, dir);
                add_new_cell(i, j, cell);

                assert(not has_pipe(ncell, opposite(dir)));
                ncell = extend_pipe(ncell, opposite(dir));
                add_new_cell(ni, nj, ncell);

                // 閉路を構成するパイプを削除(スコアの改善が最も良いものを選ぶ)
                auto loop = find_loop(grid, i, j, dir);

                int rm_i = 0, rm_j = 0, rm_dir = -1;
                int score_diff = 100000;
                int ci = i, cj = j;
                for (int k = 0; k < loop.size(); k++) {
                    int dir = loop[k];
                    if (k >= 1) {
                        auto cur = grid[ci][cj];
                        auto nxt = grid[ci + DI[dir]][cj + DJ[dir]];
                        auto rmd1 = shrink_pipe(cur, dir);
                        auto rmd2 = shrink_pipe(nxt, opposite(dir));
                        map<Cell, int> diff;
                        diff[cur]--, diff[nxt]--, diff[rmd1]++, diff[rmd2]++;
                        int temp = 0;
                        for (auto [c, d] : diff) {
                            temp += abs(target_count[c] - (count[c] + d));
                            temp -= abs(target_count[c] - count[c]);
                        }
                        if (temp < score_diff) {
                            score_diff = temp;
                            rm_i = ci;
                            rm_j = cj;
                            rm_dir = dir;
                        }
                    }

                    ci = ci + DI[dir], cj = cj + DJ[dir];
                }

                assert(ci == i and cj == j);
                assert(rm_dir >= 0);

                if (rm_dir >= 0) {
                    forn(k, 2) {
                        snapshot(rm_i, rm_j);
                        grid[rm_i][rm_j] = shrink_pipe(grid[rm_i][rm_j], rm_dir);
                        assert(get_tile(grid[rm_i][rm_j]) != 0);
                        add_new_cell(rm_i, rm_j, grid[rm_i][rm_j]);
                        rm_i += DI[rm_dir], rm_j += DJ[rm_dir];
                        rm_dir = opposite(rm_dir);
                    }
                }
            }
            // 近傍2
            else {
                assert(is_leaf(cell));

                // ncellと同色でかつパイプがncellへ伸びている
                cell = extend_pipe(clear_tile(ncell), dir);
                add_new_cell(i, j, cell);

                ncell = extend_pipe(ncell, opposite(dir));
                add_new_cell(ni, nj, ncell);

                // ncell以外の隣接セルも処理
                forn(ndir, 4) {
                    int nni = i + DI[ndir], nnj = j + DJ[ndir];
                    int edge_dir = opposite(ndir);
                    if (not in_grid(nni, nnj) or (ni == nni and nj == nnj) or not has_pipe(grid[nni][nnj], edge_dir)) {
                        continue;
                    }

                    snapshot(nni, nnj);

                    auto new_cell = shrink_pipe(grid[nni][nnj], edge_dir);

                    grid[nni][nnj] = new_cell;
                    add_new_cell(nni, nnj, new_cell);
                }
            }

            // スコア(差分)の計算
            map<int, int> diff;
            for (auto [_, new_cell] : new_cells) {
                diff[new_cell]++;
            }
            for (auto [_, old_cell] : old_cells) {
                diff[old_cell]--;
            }
            int score_diff = 0;
            for (auto [cell, d] : diff) {
                score_diff += abs(target_count[cell] - (count[cell] + d)) - abs(target_count[cell] - count[cell]);
            }

            const int new_score = score + score_diff;

            auto pr = transition_probability_min(score, new_score, temperature);

            if (rand_bool(pr)) {
                score = new_score;
                // countの更新
                for (auto [cell, d] : diff) {
                    count[cell] += d;
                }
                transition_count++;
            } else {
                // ロールバック
                for (auto [pos, cell] : old_cells) {
                    grid[pos.fst][pos.snd] = cell;
                }
            }

            if (best_score > score) {
                best_score = score;
                best_target = grid;
            }
        }

        fprintf(stderr, "diff score: %d -> %d\n", initial_diff, best_score);
        fprintf(stderr, "step: %d\n", step);
        fprintf(stderr, "transition count: %d\n", transition_count);

        assert_is_forest(best_target);

        return best_target;
    }

    // c個の連結成分からなる森であることを確認
    void assert_is_forest(const Grid& grid) {
        auto cc = count_component(grid);
        assert(cc.size() == c);
        for (auto [col, k] : cc) {
            assert(k == 1);
        }
        assert(count_invalid_edge(grid) == 0);
    }

    // countとのセルの種類ごとの差の和を計算する(余分なセルの分だけ必ず差が出ることに注意)
    int diff_cells(const Grid& grid) {
        auto temp = count;
        forn(i, n) forn(j, n) {
            temp[grid[i][j]]--;
        }
        int s = 0;
        for (auto x : temp) {
            s += abs(x);
        }
        return s;
    }

    // (si,sj)を始点としdirで始まるループに含まれる辺の列(方向の列)を返す
    vi find_loop(const Grid& grid, int si, int sj, int dir) {
        int i = si + DI[dir], j = sj + DJ[dir];
        set<pii> vis;
        auto res = _find_loop(grid, i, j, si, sj, dir, vis);
        assert(res[0] == 1);
        res.push_back(dir);
        reverse(all(res));
        res.pop_back();
        assert(res.size() % 2 == 0);
        return res;
    }

    vi _find_loop(const Grid& grid, int i, int j, int si, int sj, int pdir, set<pii>& vis) {
        if (i == si and j == sj) {
            return vi({ 1 });
        }
        vis.emplace(i, j);

        forn(dir, 4) {
            if (dir == opposite(pdir) or not has_pipe(grid[i][j], dir)) continue;
            int ni = i + DI[dir], nj = j + DJ[dir];
            if (not in_grid(ni, nj) or vis.count({ ni, nj }) > 0) continue;
            auto res = _find_loop(grid, ni, nj, si, sj, dir, vis);
            if (res[0] == 1) {
                res.push_back(dir);
                return res;
            }
        }

        return vi({ 0 });
    }

    // c個の連結成分からなる森を一つランダムに生成(公式の生成方法と同等)
    Grid random_target() {
        vec<vec<Cell>> grid = vec<vec<Cell>>(n, vec<Cell>(n));
        forn1(col, c) {
            while (true) {
                auto i = rand_range(0, n);
                auto j = rand_range(0, n);
                if (is_empty_cell(grid[i][j])) {
                    grid[i][j] = make_cell(0, col);
                    break;
                }
            }
        }

        vec<pii> candidate;
        forn(i, n) forn(j, n) {
            if (is_extendable_cell(grid, i, j)) {
                candidate.emplace_back(i, j);
            }
        }

        while (not candidate.empty()) {
            const auto k = rand_range(size_t(0), candidate.size());
            const auto [i, j] = candidate[k];

            if (not is_extendable_cell(grid, i, j)) {
                swap_remove(candidate, k);
                continue;
            }

            auto& cell = grid[i][j];
            auto col = get_color(cell);

            for (const auto dir : perm4[rand_range(size_t(0), perm4.size())]) {

                if (has_pipe(cell, dir)) {
                    continue;
                }

                int ni = i + DI[dir], nj = j + DJ[dir];
                if (in_grid(ni, nj) and is_empty_cell(grid[ni][nj])) {
                    cell = extend_pipe(cell, dir);
                    auto ncell = make_cell(extend_pipe(0, opposite(dir)), col);
                    grid[ni][nj] = ncell;
                    candidate.emplace_back(ni, nj);

                    break;
                }
            }
        }

        assert_is_forest(grid);

        return grid;
    }

    // O(n^2)
    map<int, int> count_component(const Grid& grid) {
        map<int, int> cnt;
        vec<vec<bool>> vis(n, vec<bool>(n, false));
        forn(i, n) forn(j, n) {
            if (vis[i][j]) continue;

            const int col = get_color(grid[i][j]);
            cnt[col]++;
            que<pii> q({ { i, j } });
            vis[i][j] = true;
            while (not q.empty()) {
                auto [i, j] = q.front();
                q.pop();

                const auto cell = grid[i][j];

                forn(dir, 4) {
                    if (not has_pipe(cell, dir)) continue;
                    int ni = i + DI[dir], nj = j + DJ[dir];
                    if (not in_grid(ni, nj) or vis[ni][nj]) continue;
                    const auto ncell = grid[ni][nj];
                    if (not has_pipe(ncell, opposite(dir)) or get_color(ncell) != col) continue;
                    vis[ni][nj] = true;
                    q.push({ ni, nj });
                }
            }
        }

        return cnt;
    }

    // O(n^2)
    int count_invalid_edge(const Grid& grid) {
        int c0 = 0, c1 = 0;
        forn(i, n) forn(j, n) {
            const auto cell = grid[i][j];
            for (int dir = 0; dir < 4; dir++) {
                bool p1 = has_pipe(cell, dir);
                int ni = i + DI[dir], nj = j + DJ[dir];
                bool p2 = in_grid(ni, nj) and has_pipe(grid[ni][nj], opposite(dir));
                if (p1 ^ p2 or (p1 and p2 and get_color(cell) != get_color(grid[ni][nj]))) {
                    if (in_grid(ni, nj))
                        c0++;
                    else
                        c1++;
                }
            }
        }
        assert(c0 % 2 == 0);

        return c0 / 2 + c1;
    }

    // O(n^2)
    int grid_score(const Grid& grid) {
        auto cc = count_component(grid);
        int ec = count_invalid_edge(grid);
        int score = p * ec;
        for (auto [col, k] : cc) score += k * k;
        return score;
    }
};

int main() {
    fastio();

    vi perm = { 0, 1, 2, 3 };
    do {
        perm4.push_back(perm);
    } while (next_permutation(all(perm)));

    Solver().solve();
    return 0;
}
