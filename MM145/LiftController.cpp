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

inline bool gen_bool(double p) {
    assert(0.0 <= p and p <= 1.0);
    static auto dist = uniform_real_distribution<double>(0.0, nextafter(1.0, DBL_MAX));
    return dist(rng) <= p;
}

const int MAX_STEP = 1000;
int floor_num, lift_num;
double spawn_probability;

enum Dir {
    Up,
    Down
};

class Person {
public:
    const int start_floor;
    const int start_step;

    Person(int start_floor, int start_step)
        : start_floor(start_floor), start_step(start_step) {
    }
};

class MovingPerson : public Person {
public:
    int target_floor;
    MovingPerson(int start_floor, int start_step, int target_floor)
        : Person(start_floor, start_step), target_floor(target_floor) { }
};

class WaitingPerson : public Person {
public:
    Dir dir;
    WaitingPerson(int start_floor, int start_step, Dir dir)
        : Person(start_floor, start_step), dir(dir) { }
    MovingPerson enter_lift(int target_floor) const {
        return MovingPerson(start_floor, start_step, target_floor);
    }
};

struct Lift {
    int floor_;
    vec<MovingPerson> people;
    bool closed;

    Lift(int floor)
        : floor_(floor), closed(true) { }

    bool empty() const {
        return people.empty();
    }

    bool is_full() const {
        return people.size() >= 4;
    }

    int vacancy() const {
        return 4 - people.size();
    }

    int targeting(int floor) const {
        return count_if(all(people), [&](MovingPerson p) { return p.target_floor == floor; });
    }

    bool is_ridable() const {
        return is_open() and not is_full();
    }

    void add(MovingPerson p) {
        assert(is_open());
        assert(people.size() < 4);
        people.push_back(p);
    }
    void open() {
        assert(closed);
        closed = false;
    }

    void close() {
        assert(not closed);
        closed = true;
    }

    int floor() const {
        return floor_;
    }

    bool is_closed() const {
        return closed;
    }
    bool is_open() const {
        return not is_closed();
    }

    void exit() {
        assert(not closed);
        vec<MovingPerson> cur;
        swap(people, cur);
        for (auto p : cur) {
            if (p.target_floor != floor()) people.push_back(p);
        }
    }

    void up() {
        assert(closed);
        assert(floor_ < floor_num - 1);
        floor_++;
    }

    void down() {
        assert(closed);
        assert(floor_ > 0);
        floor_--;
    }
};

struct State {
    vec<Lift> lifts;
    vec<deq<WaitingPerson>> wait_q;
    int wait_time;

    State()
        : State(vi(lift_num)) { }

    State(vi init_floor)
        : wait_time(0) {
        assert(init_floor.size() == lift_num);
        for (auto f : init_floor) {
            lifts.push_back(Lift(f));
        }

        wait_q = vec<deq<WaitingPerson>>(floor_num);
    }

    void tick() {
        forn(f, floor_num) wait_time += wait_q[f].size();
        forn(l, lift_num) wait_time += lifts[l].people.size();
    }

    void add_queue(WaitingPerson p) {
        wait_q[p.start_floor].push_back(p);
    }

    void run_exit_phase() {
        for (auto& lift : lifts) {
            if (lift.is_open()) lift.exit();
        }
    }

    void enter_lift(int lift, int target_floor) {
        const auto floor = lifts[lift].floor();
        assert(not wait_q[floor].empty());
        const auto person = wait_q[floor].front();
        wait_q[floor].pop_front();

        assert(target_floor != floor);
        assert((person.dir == Up and target_floor > person.start_floor) or (person.dir == Down and target_floor < person.start_floor));
        assert(floor == person.start_floor);

        lifts[lift].add(person.enter_lift(target_floor));
    }
};

struct Command {
    map<int, string> commands;
    bool contains(int lift) {
        return commands.count(lift) > 0;
    }
    void add(int lift, string command) {
        assert(not contains(lift));
        commands[lift] = command;
    }
    size_t size() {
        return commands.size();
    }
    void write() {
        assert(size() == lift_num);
        for (auto [_, command] : commands) {
            cout << command << endl;
        }
    }
};

int direction(int from, int to) {
    if (to > from) return 1;
    if (to == from) return 0;
    return -1;
}

struct HiddenParam {
    vec<double> floor_spawn_probability;
};

struct LiftPhase {
    Command command;
    State state;
    HiddenParam hiddenParam;
    LiftPhase(State state, HiddenParam hiddenParam)
        : state(state), hiddenParam(hiddenParam) { }
    Command run() {
        vec<tuple<int, int, int>> source;
        const int WAIT_TIME_INF = 100000;
        vec<vi> schedule(lift_num);
        vec<tuple<int, int, int, int>> dist_lift_floor;

        vi floor_people(floor_num);
        forn(f, floor_num) floor_people[f] = state.wait_q[f].size();

        forn(l, lift_num) {
            auto& lift = state.lifts[l];
            const int cf = lift.floor();

            // (有人の)リフトの搭乗者の行き先について訪問順を最適化
            if (not lift.empty() and lift.is_closed()) {
                map<int, int> count;

                for (auto p : lift.people) {
                    count[p.target_floor]++;
                }

                vi perm;
                for (auto kv : count) {
                    perm.push_back(kv.fst);
                }

                int best_wait_time = WAIT_TIME_INF;

                // 訪問順を全列挙
                do {
                    int k = (int)lift.people.size();
                    int wait_time = 0;
                    int floor = lift.floor();
                    for (auto next_floor : perm) {
                        // 移動からドアを開くまでの待ち時間
                        wait_time += (abs(next_floor - floor) + 1) * k;
                        k -= count[next_floor];
                        // ドアを閉じるのにかかる待ち時間
                        wait_time += k;

                        floor = next_floor;
                    }
                    if (best_wait_time > wait_time) {
                        best_wait_time = wait_time;
                        schedule[l] = perm;
                    }
                } while (next_permutation(all(perm)));
            }

            // 無人のリフトについて有人フロアへの距離を計算
            if (lift.empty() and lift.is_closed()) {
                forn(f, floor_num) {
                    if (not state.wait_q[f].empty()) {
                        dist_lift_floor.emplace_back(abs(f - cf), -state.wait_q[f].size(), l, f);
                    }
                }
            }
        }

        forn(l, lift_num) {
            const auto& lift = state.lifts[l];
            // 確定で開くリフトの分フロアの人数を減らす
            if (not schedule[l].empty() and lift.floor() == schedule[l][0]) {
                floor_people[lift.floor()] -= min(floor_people[lift.floor()], lift.vacancy() + lift.targeting(lift.floor()));
            }
        }

        // 無人リフトと有人フロアの組について距離の近いものから貪欲に採用
        // 距離がタイの場合は多い方
        sort(all(dist_lift_floor));
        set<int> used_floor, used_lift;
        for (auto [d, c, l, f] : dist_lift_floor) {
            if (not used_floor.count(f) and not used_lift.count(l) and floor_people[f] > 0) {
                schedule[l] = { f };
                used_floor.insert(f);
                used_lift.insert(l);
            }
        }

        // 現在のフロアに対してドアを開くか決定する
        vec<bool> open(lift_num);

        vi exit(floor_num);
        // 1.現在フロアが目的フロア
        forn(floor, floor_num) {
            forn(l, lift_num) {
                const auto& lift = state.lifts[l];
                if (lift.is_open() or lift.floor() != floor or schedule[l].empty()) continue;
                int lift_dir = direction(floor, schedule[l][0]);
                if (lift_dir == 0) {
                    open[l] = true;
                    exit[floor] += lift.vacancy() + lift.targeting(floor);
                }
            }
        }

        // 2.リフトの進行方向と目的地の方向が一致する乗客を乗せる意図
        vec<vi> type2(floor_num);
        forn(floor, floor_num) {
            for (int l = 0; l < lift_num; l++) {
                const auto& lift = state.lifts[l];
                if (lift.is_open() or lift.floor() != floor or lift.is_full() or schedule[l].empty()) continue;
                int lift_dir = direction(floor, schedule[l][0]);
                if (lift_dir != 0) {
                    type2[floor].push_back(l);
                }
            }
        }

        // ドアを開くリフトを決める
        // 方向に関する条件を満たした上で、最少リフト数でフロアの乗客を網羅する、網羅できない場合なるべく多く搭乗させる
        forn(floor, floor_num) {
            int covered = exit[floor];
            int lift_count = 0;
            vi best;

            // リフトの開き方のパターンを列挙
            forn(pattern, 1 << type2[floor].size()) {
                int k = exit[floor];
                vi cur;
                forn(i, type2[floor].size()) {
                    if (not testb(pattern, i)) continue;
                    const auto l = type2[floor][i];
                    const auto& lift = state.lifts[l];
                    cur.push_back(l);
                    k += lift.vacancy() + lift.targeting(floor);
                }

                // 高々k人の進行方向
                int dir = 0;
                forn(i, min(state.wait_q[floor].size(), size_t(k))) {
                    dir += state.wait_q[floor][i].dir == Up ? 1 : -1;
                }

                int bal = 0;
                for (auto l : cur) {
                    assert(not schedule[l].empty());
                    int lift_dir = direction(floor, int(schedule[l][0]));
                    if (dir * lift_dir <= 0)
                        bal--;
                    else
                        bal++;
                }
                if (bal <= 0) continue;

                // フロアを網羅する範囲でリフト数最小化,網羅できないならば人数を最大化
                if (covered >= state.wait_q[floor].size()) {
                    if (k >= state.wait_q[floor].size() and popcnt(pattern) < lift_count) {
                        lift_count = popcnt(pattern);
                        covered = k;
                        best = cur;
                    }
                } else {
                    if (covered < k) {
                        lift_count = popcnt(pattern);
                        covered = k;
                        best = cur;
                    }
                }
            }

            for (auto l : best) {
                open[l] = true;
            }
        }

        vec<tuple<double, int, int>> eval_lift_floor;
        forn(l, lift_num) {
            auto& lift = state.lifts[l];
            if (lift.is_open()) {
                if (lift.empty()) {
                    used_floor.insert(lift.floor());
                }
                close_door(l);
            } else {
                if (open[l]) {
                    open_door(l);
                } else if (not schedule[l].empty()) {
                    move_lift(l, schedule[l][0], true);
                } else {
                    forn(f, floor_num) {
                        if (not state.wait_q[f].empty()) continue;
                        double d = sqrt(sqrt(abs(f - lift.floor()) + 1));
                        const double prob = hiddenParam.floor_spawn_probability[f];
                        // 出現確率が高く,距離が近いフロア
                        eval_lift_floor.emplace_back(prob / d, l, f);
                    }
                }
            }
        }

        // 無人リフトと無人フロアの組について評価値の大きいものから貪欲に採用
        sort(all(eval_lift_floor));
        reverse(all(eval_lift_floor));
        for (auto [e, l, f] : eval_lift_floor) {
            if (command.contains(l) or used_floor.count(f) or used_lift.count(l)) continue;
            used_floor.insert(f);
            used_lift.insert(l);
            move_lift(l, f, true);
        }

        // 残りはランダムに動く
        forn(l, lift_num) {
            if (command.contains(l)) continue;
            auto target_floor = rand_range(0, floor_num);
            move_lift(l, target_floor, false);
        }

        return command;
    }

    void open_door(int lift) {
        state.lifts[lift].open();
        command.add(lift, "open");
    }

    void close_door(int lift) {
        assert(not command.contains(lift));
        state.lifts[lift].close();
        command.add(lift, "close");
    }

    void move_lift(int lift, int target_floor, bool open_same_floor) {
        assert(not command.contains(lift));

        if (target_floor < 0) {
            stay(lift);
            return;
        }

        int cf = state.lifts[lift].floor();
        if (target_floor < cf) {
            state.lifts[lift].down();
            command.add(lift, "down");
        } else if (target_floor == cf) {
            if (open_same_floor) {
                open_door(lift);
            } else {
                stay(lift);
            }
        } else {
            assert(target_floor > cf);
            state.lifts[lift].up();
            command.add(lift, "up");
        }
    }

    void stay(int lift) {
        assert(not command.contains(lift));
        command.add(lift, "stay");
    }
};

struct Solver {
    State state;
    int elapsed = 0;

    Solver() {
        cin >> floor_num >> lift_num >> spawn_probability;
        vi current_floor(lift_num);
        forn(l, lift_num) {
            cin >> current_floor[l];
            current_floor[l]--;
        }
        state = State(current_floor);
    }

    void solve() {
        vi spawn_count(floor_num);

        forn(step, MAX_STEP) {
            state.tick();

            // queue phase
            {
                int n;
                cin >> n;
                // WARNING:
                // 同じターンに同じフロアに現れた人たちについて,テスター内部のキューにおける順序と
                // プログラムの入力として与えられる順序は逆になっている
                map<int, vec<WaitingPerson>> qs;
                forn(i, n) {
                    int start_floor;
                    char dir;
                    cin >> start_floor >> dir;
                    start_floor--;
                    spawn_count[start_floor]++;
                    qs[start_floor].push_back(WaitingPerson(start_floor, step, dir == 'U' ? Up : Down));
                }
                for (auto [f, q] : qs) {
                    for (int i = q.size() - 1; i >= 0; i--) {
                        state.add_queue(q[i]);
                    }
                }
            }

            // exit phase
            state.run_exit_phase();

            // entry phase
            {
                int e;
                cin >> e;
                forn(i, e) {
                    int lift, target_floor;
                    cin >> lift >> target_floor;
                    target_floor--;
                    state.enter_lift(lift, target_floor);
                }
            }
            cin >> elapsed;

            // lift phase
            vec<double> floor_spawn_probability = vec<double>(floor_num);
            forn(i, floor_num) {
                double x = 1.0 * spawn_count[i] / MAX_STEP;
                double y = spawn_probability / 2.0 * (MAX_STEP - step - 1) / MAX_STEP;
                floor_spawn_probability[i] = x + y;
            }
            const HiddenParam hiddenParam = {
                floor_spawn_probability
            };

            auto lp = LiftPhase(state, hiddenParam);
            lp.run().write();
            state = move(lp.state);
        }
    }
};

int main() {
    fastio();
    Solver().solve();
    return 0;
}
