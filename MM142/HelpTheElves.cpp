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
using vb = vec<bool>;
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

const int DI[4] = { -1, 0, 1, 0 };
const int DJ[4] = { 0, 1, 0, -1 };
const string DIR = "URDL";

// 最終目的地と移動方向の列
using Path = tuple<int, int, vi>;

struct Solver {
    int n, cost, money;
    double elf_p;
    vec<string> grid, reservation;

    // 解
    string moves;

    // エルフ,プレゼント,箱に共通のID
    vec<vi> id_map;
    // mapのデフォルトが0なので1から
    int id_gen = 1;
    // id -> coordinate
    map<int, pii> pos;

    // 連結成分(木,箱,箱持ちが壁)
    // プレゼントを含む場合は偶,そうでなければ奇とする
    vec<vi> component;

    // ゲート候補
    vec<vb> is_candidate_gate;

    // 開いているゲート
    set<int> open_id;
    vec<vec<tuple<int, int, int>>> close_info;

    // 除去する箱および箱持ち
    set<int> removal;

    set<int> target;

    // 集計用
    int present_total = 0;
    int present_picked = 0;
    int present_stolen = 0;
    int box_total = 0;
    int box_picked = 0;
    int box_stolen = 0;
    int elf_count = 0;

    Solver() {
        cin >> n >> cost >> elf_p >> money;
        grid = vec<string>(n, string(n, '.'));
        reservation = grid;
        id_map = vec<vi>(n, vi(n, 0));
        component = vec<vi>(n, vi(n, 0));
        is_candidate_gate = vec<vb>(n, vb(n));
    }

    void solve() {
        int elapsed_time;

        forn(step, n * n) {
            cin >> elapsed_time >> money;

            forn(i, n) forn(j, n) {
                cin >> grid[i][j];

                if (step == 0 and is_present(i, j)) {
                    present_total++;
                }

                if (reservation[i][j] == '.' and not is_empty(i, j)) {
                    id_map[i][j] = id_gen++;
                    if (is_elf(i, j)) {
                        elf_count++;
                    }
                    if (is_box(i, j)) {
                        box_total++;
                    }

                    pos[id_map[i][j]] = { i, j };
                }
            }

            if (elapsed_time > 8500) {
                cout << "-1" << endl;
                continue;
            }

            // 連結成分を更新
            forn(i, n) forn(j, n) component[i][j] = 0;
            int c = 2;
            forn(i, n) forn(j, n) {
                if (is_present(i, j) and component[i][j] == 0) {
                    bfs_cc(i, j, c);
                    c += 2;
                }
            }

            c = 1;
            forn(i, n) forn(j, n) {
                if (component[i][j] == 0) {
                    bfs_cc(i, j, c);
                    c += 2;
                }
            }

            moves.clear();
            target.clear();

            // プレゼントの移動
            forn(i, n) forn(j, n) {
                int ti, tj;
                vi dirs;
                if (is_free_elf(i, j)) {
                    tie(ti, tj, dirs) = find_nearest_present(i, j);

                    if (not dirs.empty()) {
                        assert(id_map[ti][tj] > 0);
                    }

                } else if (is_present_carrier(i, j)) {
                    if (is_edge(i, j)) {
                        present_stolen++;
                        tie(ti, tj, dirs) = find_adjacent_outside(i, j);
                    } else {
                        tie(ti, tj, dirs) = find_nearest_edge(i, j);
                    }
                }

                if (not dirs.empty()) {
                    // fprintf(stderr, "(%d) 1: (%d,%d,%d) -> final(%d,%d)\n", step, i, j, dirs[0], ti, tj);
                    make_move(i, j, dirs[0], dirs[1]);
                }
            }

            // ゲート化
            {
                // 現時点でのゲート化の候補を計算
                forn(i, n) forn(j, n) is_candidate_gate[i][j] = false;
                forn(i, n) forn(j, n) {
                    if (not is_box(i, j)) {
                        continue;
                    }

                    int open = 0;
                    set<int> cs;
                    forn(dir, 4) {
                        int ni, nj;
                        tie(ni, nj) = neighbor(i, j, dir);
                        if (in_grid(ni, nj)) {
                            if (is_empty(ni, nj) or is_free_elf(ni, nj) or is_present(ni, nj)) {
                                open++;
                            }
                            // 2回続けてゲートを通る場合もあるので(隣接する)ゲートは排除できない
                            if (not is_wall(ni, nj)) {
                                cs.insert(component[ni][nj]);
                            }
                        }
                    }

                    // 進入方向と脱出方向とゲートの移動方向はそれぞれ異なるべき
                    // また異なる連結成分に接しているべき
                    if (open < 3 or cs.size() < 2) {
                        continue;
                    }

                    // 単体
                    forn(dir, 4) {
                        bool ok1 = false;
                        bool ok2 = false;
                        forn(k, 4) {
                            int ni, nj;
                            tie(ni, nj) = neighbor(i, j, k);

                            if (dir % 2 == k % 2) {
                                ok1 |= in_grid(ni, nj) and (is_empty(ni, nj) or is_movable(ni, nj));
                            } else {
                                ok2 |= in_grid(ni, nj) and (is_empty(ni, nj) or is_free_elf(ni, nj));
                            }
                        }
                        if (ok1 and ok2) {
                            is_candidate_gate[i][j] = true;
                        }
                    }
                }

                forn(i, n) forn(j, n) {
                    if (is_free_elf(i, j)) {
                        int ti, tj;
                        vi dirs;
                        tie(ti, tj, dirs) = find_nearest_candidate_gate(i, j);

                        if (not dirs.empty()) {
                            // fprintf(stderr, "(%d) 2: (%d,%d,%d) -> final(%d,%d)\n", step, i, j, dirs[0], ti, tj);
                            make_move(i, j, dirs[0], dirs[1]);
                        }
                    }
                }
            }

            // ゲートを閉じる
            {
                vec<vec<tuple<int, int, int>>> temp;

                forn(idx, close_info.size()) {
                    assert(not close_info[idx].empty());

                    int i, j, dir;
                    tie(i, j, dir) = close_info[idx][0];

                    // 除去されるなどしてopen_idに含まれていない
                    if (open_id.count(id_map[i][j]) == 0) {
                        continue;
                    }

                    int ni, nj;
                    tie(ni, nj) = neighbor(i, j, dir);

                    // 1つ目の要素を戻せるなら全部戻せる
                    if (is_empty(ni, nj)) {
                        forn(jdx, close_info[idx].size()) {
                            int i, j, dir;
                            tie(i, j, dir) = close_info[idx][jdx];
                            assert(open_id.count(id_map[i][j]));
                            open_id.erase(id_map[i][j]);
                            // fprintf(stderr, "(%d) 4: (%d,%d,%d)(%c) -> next(%d,%d)\n", step, i, j, dir, grid[i][j], ni, nj);
                            bool ok_closing_gate = make_move(i, j, dir, -1);
                            assert(ok_closing_gate);
                        }
                    } else {
                        temp.push_back(close_info[idx]);
                    }
                }

                close_info = temp;
            }

            // 単一の連結成分に接している箱,箱持ちを除去
            // 除去可能なものを計算
            forn(i, n) forn(j, n) {
                if (not is_box_carrier(i, j) and not is_box(i, j)) {
                    continue;
                }

                set<int> cs;
                forn(k, 4) {
                    int ni, nj;
                    tie(ni, nj) = neighbor(i, j, k);
                    if (in_grid(ni, nj) and not is_wall(ni, nj) and not is_box_carrier(ni, nj)) {
                        cs.insert(component[ni][nj]);
                    }
                }

                // 異なる連結成分に接していないなら除去
                if (cs.size() <= 1) {
                    removal.insert(id_map[i][j]);
                }
            }

            // 除去する箱に取り付くように指示
            forn(i, n) forn(j, n) {
                if (not is_free_elf(i, j)) {
                    continue;
                }

                int ti, tj;
                vi dirs;
                tie(ti, tj, dirs) = find_nearest(
                    i,
                    j,
                    [&](int ti, int tj) {
                        int id = id_map[ti][tj];
                        return is_box(ti, tj) and removal.count(id);
                    },
                    [&](int ti, int tj) { return false; });

                if (not dirs.empty()) {
                    make_move(i, j, dirs[0], dirs[1]);
                }
            }

            // 除去する箱持ちへ指示
            forn(i, n) forn(j, n) {
                const int id = id_map[i][j];
                if (not is_box_carrier(i, j) or removal.count(id) == 0) {
                    continue;
                }

                int ti, tj;
                vi dirs;
                if (is_edge(i, j)) {
                    box_stolen++;
                    tie(ti, tj, dirs) = find_adjacent_outside(i, j);
                } else {
                    tie(ti, tj, dirs) = find_nearest_edge(i, j);
                }

                if (not dirs.empty()) {
                    make_move(i, j, dirs[0], dirs[1]);
                }
            }

            if (moves.empty()) moves = "-1";

            // cerr << moves << endl;
            cout << moves << endl;

            if (present_total == present_stolen) {
                break;
            }

            // 前回の状態をコピー
            reservation = grid;
        }

        fprintf(stderr, "elf: %d\n", elf_count);
        fprintf(stderr, "box: %d / %d / %d\n", box_stolen, box_picked, box_total);
        fprintf(stderr, "present: %d / %d / %d\n", present_stolen, present_picked, present_total);
        fprintf(stderr, "=====================\n\n");
    }

    bool in_grid(int i, int j) {
        return 0 <= i and i < n and 0 <= j and j < n;
    }

    // (i,j)にいる妖精をdir1方向に(その後さらにdir2に進むべく)動かす.具体的には以下の事を行う.
    // 1.解を更新する
    // 2.pos,id_mapを適切に更新する
    // 3.grid[i][j]を空('.')にする
    // 4.(もし(ni,nj)が存在すれば)grid[ni][nj]を予約済み('X')とする
    bool make_move(int i, int j, int dir1, int dir2) {
        // fprintf(stderr, "(%d,%d) %d -> %d\n", i, j, dir1, dir2);
        assert(is_elf(i, j));

        // 移動先のセルがゲートならまずそれを開けてもらう
        {
            int ni, nj;
            tie(ni, nj) = neighbor(i, j, dir1);
            if (in_grid(ni, nj) and is_gate(ni, nj, rev_dir(dir1), dir2)) {
                const int nid = id_map[ni][nj];

                // すでに操作中のゲート
                if (open_id.count(nid)) {
                    dir1 = -1;
                } else {
                    bool open_request_accepted = open_request(ni, nj, rev_dir(dir1), dir2);
                    // assert(open_request_accepted);
                    if (not open_request_accepted) {
                        dir1 = -1;
                    }
                }
            }

            // ゲートを動かせなかった
            if (dir1 < 0) {
                return false;
            }
        }

        const int id = id_map[i][j];
        id_map[i][j] = 0;
        pos.erase(id);

        moves += to_string(i) + " " + to_string(j) + " " + DIR[dir1] + " ";

        const int ni = i + DI[dir1], nj = j + DJ[dir1];

        if (in_grid(ni, nj)) {
            assert(not is_reserved(ni, nj));
            assert(not is_free_elf(i, j) or (is_empty(ni, nj) or is_movable(ni, nj)));
            assert(not is_carrier_elf(i, j) or is_empty(ni, nj));

            pos[id] = { ni, nj };
            const int nid = id_map[ni][nj];

            if (is_present(ni, nj)) {
                present_picked++;
                pos.erase(nid);
            }

            if (is_box(ni, nj)) {
                box_picked++;
                pos.erase(nid);
            }

            id_map[ni][nj] = id;

            grid[ni][nj] = 'X';
        }

        grid[i][j] = '.';

        return true;
    }

    // (i,j)から見てdir_inから進入しdir_outへ進むために開くことができるどうか
    // 開ける場合は(i,j)についてmovesも更新する
    bool open_request(int i, int j, int dir_in, int dir_out) {
        assert(is_box_carrier(i, j));

        const int dir = as_gate1(i, j, dir_in, dir_out);

        if (dir < 0) {
            return false;
        }

        int ni, nj;
        tie(ni, nj) = neighbor(i, j, dir);

        assert(in_grid(ni, nj) and is_empty(ni, nj));

        bool ok_as_next_cell_is_empty = make_move(i, j, dir, -1);
        assert(ok_as_next_cell_is_empty);

        open_id.insert(id_map[ni][nj]);

        close_info.push_back({ { ni, nj, (dir + 2) % 4 } });

        return true;
    }

    // 木,箱,箱持ちを壁として(i,j)の連結成分を計算する.
    void bfs_cc(const int i, const int j, const int c) {
        component[i][j] = c;
        que<pii> q({ { i, j } });
        while (not q.empty()) {
            int i, j;
            tie(i, j) = q.front();
            q.pop();

            forn(k, 4) {
                int ni = i + DI[k], nj = j + DJ[k];
                if (not in_grid(ni, nj) or is_wall(ni, nj) or is_box_carrier(ni, nj) or component[ni][nj] != 0) {
                    continue;
                }
                q.emplace(ni, nj);
                component[ni][nj] = c;
            }
        }
    }

    Path find_nearest_present(const int i, const int j) {
        return find_nearest(
            i,
            j,
            [&](int i, int j) { return is_present(i, j); },
            [&](int i, int j) { return false; });
    }

    Path find_nearest_box(const int i, const int j) {
        return find_nearest(
            i,
            j,
            [&](int i, int j) { return is_box(i, j); },
            [&](int i, int j) { return false; });
    }

    // ゲート候補の構成要素を見つける
    Path find_nearest_candidate_gate(const int i, const int j) {
        return find_nearest(
            i,
            j,
            [&](int i, int j) { return is_box(i, j) and is_candidate_gate[i][j]; },
            [&](int i, int j) { return false; });
    }

    // 見つからない場合は操作列が空,そうなければ操作列の末尾は-1
    Path find_adjacent_outside(int i, int j) {
        assert(is_edge(i, j));

        int dir = 0;
        if (i == 0)
            dir = 0;
        else if (i == n - 1)
            dir = 2;
        else if (j == 0)
            dir = 3;
        else if (j == n - 1) {
            dir = 1;
        } else {
            return { -1, -1, {} };
        }

        return { i, j, { dir, -1 } };
    }

    Path find_nearest_edge(int i, int j) {
        return find_nearest(
            i,
            j,
            [&](int i, int j) { return is_edge(i, j) and is_empty(i, j); },
            [&](int i, int j) { return false; });
    }

    // pred(ti,tj)を満たす(i,j)でない最も近い目的地の座標(ti,tj)と移動方向からなる操作列を返す.
    // ただし見つからない場合は操作列が空,そうなければ操作列の末尾は-1.
    // 以下で節点は「座標と(ゲートであれば)そのゲートを動かした方向」に対応する.
    // 通行可能なのは(is_emtpy or is_box_carrier or is_allowed)
    Path find_nearest(const int si, const int sj, function<bool(int, int)> pred, function<bool(int, int)> is_allowed) {
        auto is_passable_normal = [&](int i, int j) -> bool {
            return (is_empty(i, j) or is_allowed(i, j)) and not open_id.count(id_map[i][j]);
        };

        auto is_passable_gate = [&](int i, int j) -> bool {
            return (is_box_carrier(i, j) or is_allowed(i, j)) and not open_id.count(id_map[i][j]);
        };

        que<tuple<int, int, int>> q({ { si, sj, -1 } });
        // ゲート(簡単のため箱持ちかどうかだけ判定)の場合は第３要素が動かした方向
        set<tuple<int, int, int>> vis({ { si, sj, -1 } });

        // (i,j,このセルのゲートを動かした方向) -> (このセルへの進入方向,直前のセルのゲートを動かした方向)
        map<tuple<int, int, int>, pii> in_dir;
        in_dir[{ si, sj, -1 }] = { -1, -1 }; // 番兵

        while (not q.empty()) {
            int i, j, dir_move;
            tie(i, j, dir_move) = q.front();

            q.pop();

            forn(dir_in, 4) {
                // (i,j)がゲートの時(ni,nj)はゲートの移動先である可能性がある
                if (dir_move == dir_in) {
                    continue;
                }

                int ni, nj;
                tie(ni, nj) = neighbor(i, j, dir_in);

                if (not in_grid(ni, nj)) {
                    continue;
                }

                if (pred(ni, nj)) {
                    vi path = { dir_in };

                    int pi = ni, pj = nj;
                    int d_prev_move = dir_move;
                    int d_cur = dir_in;

                    // パスの復元
                    while (d_cur >= 0) {
                        if (path.size() >= 2000) break;
                        tie(pi, pj) = neighbor(pi, pj, rev_dir(d_cur));

                        assert(in_grid(pi, pj));

                        auto p = in_dir[{ pi, pj, d_prev_move }];
                        tie(d_cur, d_prev_move) = p;
                        path.push_back(d_cur);
                    }
                    assert(path.back() == -1);
                    path.pop_back();
                    reverse(all(path));
                    path.push_back(-1);

                    assert(pi == si and pj == sj);

                    return { ni, nj, path };
                }

                if (is_box_carrier(ni, nj)) {
                    if (not is_passable_gate(ni, nj)) {
                        continue;
                    }

                    forn(dir_move_cur, 4) {
                        // 進入方向と等しい
                        if ((dir_move_cur + 2) % 4 == dir_in) {
                            continue;
                        }

                        if (vis.count({ ni, nj, dir_move_cur })) {
                            continue;
                        }

                        int nni, nnj;
                        tie(nni, nnj) = neighbor(ni, nj, dir_move_cur);

                        if (in_grid(nni, nnj) and is_empty(nni, nnj)) {
                            q.emplace(ni, nj, dir_move_cur);
                            vis.emplace(ni, nj, dir_move_cur);
                            in_dir[{ ni, nj, dir_move_cur }] = { dir_in, dir_move };
                        }
                    }

                } else {
                    if (vis.count({ ni, nj, -1 }) or not is_passable_normal(ni, nj)) {
                        continue;
                    }

                    q.emplace(ni, nj, -1);
                    vis.emplace(ni, nj, -1);
                    in_dir[{ ni, nj, -1 }] = { dir_in, dir_move };
                }
            }
        }

        return { -1, -1, {} };
    }

    int rev_dir(int dir) {
        return (dir + 2) % 4;
    }

    bool is(int i, int j, char c) {
        return grid[i][j] == c;
    }

    bool is_empty(int i, int j) {
        return is(i, j, '.');
    }

    bool is_tree(int i, int j) {
        return is(i, j, 'T');
    }

    bool is_reserved(int i, int j) {
        return is(i, j, 'X');
    }

    bool is_wall(int i, int j) {
        return is_tree(i, j) or is_box(i, j);
    }

    bool is_present(int i, int j) {
        return is(i, j, 'P');
    }

    bool is_box(int i, int j) {
        return is(i, j, 'b');
    }

    // 妖精が移送可能なオブジェクト
    bool is_movable(int i, int j) {
        return is_present(i, j) or is_box(i, j);
    }

    bool is_present_carrier(int i, int j) {
        return is(i, j, 'E');
    }

    bool is_box_carrier(int i, int j) {
        return is(i, j, 'B');
    }

    bool is_carrier_elf(int i, int j) {
        return is_present_carrier(i, j) or is_box_carrier(i, j);
    }

    bool is_free_elf(int i, int j) {
        return is(i, j, 'e');
    }

    bool is_elf(int i, int j) {
        return is_carrier_elf(i, j) or is_free_elf(i, j);
    }

    bool is_edge(int i, int j) {
        return i == 0 or i == n - 1 or j == 0 or j == n - 1;
    }

    // (i,j)から見てdir_inから入り,dir_outから出る場合のゲートの移動方向
    // 移動不可なら-1
    int as_gate1(int i, int j, int dir_in, int dir_out) {
        if (not is_box_carrier(i, j)) return -1;
        forn(k, 4) { // このセルを動かす方向
            if (k == dir_in or k == dir_out) {
                continue;
            }
            int ni, nj;
            tie(ni, nj) = neighbor(i, j, k);
            if (in_grid(ni, nj) and is_empty(ni, nj)) {
                return k;
            }
        }
        return -1;
    }

    bool is_gate1(int i, int j, int dir_in, int dir_out) {
        return as_gate1(i, j, dir_in, dir_out) >= 0;
    }

    bool is_gate(int i, int j, int dir_in, int dir_out) {
        return is_gate1(i, j, dir_in, dir_out);
    }

    pii neighbor(int i, int j, int dir) {
        int ni = i + DI[dir], nj = j + DJ[dir];
        return { ni, nj };
    }
};

int main() {
    fastio();
    Solver().solve();
    return 0;
}
