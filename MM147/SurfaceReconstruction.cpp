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

using Rng = mt19937_64;
Rng rng(7241567);
template <typename T, typename R>
inline typename enable_if<is_integral<T>::value, T>::type rand_range(T l, T r, R& rng) {
    assert(l < r);
    return uniform_int_distribution<T>(l, r - 1)(rng);
}

template <typename T, typename R>
inline typename enable_if<is_floating_point<T>::value, T>::type rand_range(T l, T r, R& rng) {
    assert(l <= r);
    return uniform_real_distribution<double>(l, r)(rng);
}

template <typename R>
inline bool rand_bool(double p, R& rng) {
    assert(0.0 <= p and p <= 1.0);
    static auto dist = uniform_real_distribution<double>(0.0, 1.0);
    return dist(rng) < p;
}

template <typename T>
class WeightedIndex {
private:
    const size_t n;
    vector<T> cumulative_weight;

public:
    WeightedIndex(const vector<T>& weights) :
        n(weights.size()) {
        assert(weights.size() > 0);
        cumulative_weight.resize(n);
        partial_sum(weights.begin(), weights.end(), cumulative_weight.begin());
        assert(cumulative_weight.back() > 0);
    }

    template <typename R>
    size_t operator()(R& rng) const {
        T x = rand_range<T>(T(0), cumulative_weight.back(), rng);

        long long l = -1, r = n - 1;
        while (r - l > 1) {
            auto m = (l + r) / 2;
            T v = cumulative_weight[m];
            if (x >= v)
                l = m;
            else
                r = m;
        }
        return (size_t)r;
    }
};

using Clock = chrono::high_resolution_clock;
using Duration = Clock::duration;
class Timer {
private:
    chrono::time_point<Clock> begin;
    chrono::time_point<Clock> prev;
public:
    Timer(){reset();}
    static Timer start(){return Timer();}
    void reset() { begin = Clock::now(); prev = begin; }
    Duration elapsed() const {return Clock::now() - begin;}
    Duration lap() { auto temp = prev; prev = Clock::now(); return prev - temp; }
};

inline ll as_millis(const Duration& dur) { return chrono::duration_cast<chrono::milliseconds>(dur).count(); }
inline ll as_micros(const Duration& dur) { return chrono::duration_cast<chrono::microseconds>(dur).count(); }
inline constexpr Duration from_millis(ll millis) { return chrono::milliseconds(millis); }
inline constexpr Duration from_micros(ll micros) { return chrono::microseconds(micros); }
struct Scheduler {
    const double t0, t1;
    const Duration time_limit;
    const Timer sw;
    Scheduler(double t0, double t1, Duration time_limit) :
        t0(t0), t1(t1), time_limit(time_limit), sw(Timer::start()) {}
    double temperature() const {
        double progression = 1.0 * as_micros(sw.elapsed()) / as_micros(time_limit);
        if (progression > 1.0) { return -1.0; }
        else { return pow(t0, 1.0 - progression) * pow(t1, progression); }
    }
};


template <typename T>
double transition_probability_min(T delta, double temperature) { return delta <= 0.0 ? 1.0 : exp(-delta / temperature); }
template <typename T>
void swap_remove(vec<T> &v, size_t i) {
    assert(i < v.size());
    swap(v[i],v[v.size()-1]);
    v.pop_back();
}
// clang-format on

const vi DI = { -1, -1, 0, 1, 1, 1, 0, -1 };
const vi DJ = { 0, 1, 1, 1, 0, -1, -1, -1 };
const Duration TL = from_millis(10000);
const Timer TIMER = Timer::start();
const int E_MIN = 2;
const int E_MAX = 30;
int N;
double A;

struct Point {
    int y, x;
    Point(int y, int x) : y(y), x(x) { }
    int dist2(const Point& other) const
    {
        int dy = y - other.y;
        int dx = x - other.x;
        return dy * dy + dx * dx;
    }
    operator size_t() const
    {
        return y * N + x;
    }
};

struct Equation {
    virtual double operator()(const Point& p) = 0;
    virtual ~Equation() { }
    virtual unique_ptr<Equation> delta() = 0;
    virtual unique_ptr<Equation> clone() = 0;
};

struct Slope : Equation {
    constexpr const static double S_MIN = -10.;
    constexpr const static double S_MAX = 10.;
    double s1, s2;
    Point offset;
    Slope(Point offset) : s1(rand_range(S_MIN, S_MAX, rng)), s2(rand_range(S_MIN, S_MAX, rng)), offset(offset) { }
    double operator()(const Point& p)
    {
        return (p.x - offset.x) * s1 - (p.y - offset.y) * s2;
    }
    void clamp()
    {
        this->offset.x = max(0, min(N, this->offset.x));
        this->offset.y = max(0, min(N, this->offset.y));
        this->s1 = max(S_MIN, min(S_MAX, this->s1));
        this->s2 = max(S_MIN, min(S_MAX, this->s2));
    }
    unique_ptr<Equation> delta()
    {
        auto* r = new Slope(*this);
        const int ty = rand_range(0, 3, rng);
        if (ty == 0)
        {
            const size_t dir = rand_range(size_t(0), DI.size(), rng);
            r->offset.y += DI[dir];
            r->offset.x += DJ[dir];
        }
        else if (ty == 1)
        {
            r->s1 += rand_bool(0.5, rng) ? 0.01 : -0.01;
        }
        else
        {
            r->s2 += rand_bool(0.5, rng) ? 0.01 : -0.01;
        }
        r->clamp();
        return unique_ptr<Equation>(r);
    }
    unique_ptr<Equation> clone()
    {
        return unique_ptr<Equation>(new Slope(*this));
    }
};
constexpr const double Slope::S_MIN;
constexpr const double Slope::S_MAX;

struct SinCos : Equation {
    constexpr const static double S_MIN = -0.4;
    constexpr const static double S_MAX = 0.4;
    constexpr const static double AMP_MIN = 10.0;
    constexpr const static double AMP_MAX = 100.0;
    double s1, s2, amp;
    Point offset;
    SinCos(Point offset) :
        s1(rand_range(S_MIN, S_MAX, rng)),
        s2(rand_range(S_MIN, S_MAX, rng)),
        amp(rand_range(AMP_MIN, AMP_MAX, rng)),
        offset(offset)
    {
    }
    double operator()(const Point& p)
    {
        return amp * (sin((p.x - offset.x) * s1) + cos((p.y - offset.y) * s2));
    }
    void clamp()
    {
        this->offset.x = max(0, min(N, this->offset.x));
        this->offset.y = max(0, min(N, this->offset.y));
        this->s1 = max(S_MIN, min(S_MAX, this->s1));
        this->s2 = max(S_MIN, min(S_MAX, this->s2));
        this->amp = max(AMP_MIN, min(AMP_MAX, this->amp));
    }
    unique_ptr<Equation> delta()
    {
        auto* r = new SinCos(*this);
        const int ty = rand_range(0, 4, rng);
        if (ty == 0)
        {
            const size_t dir = rand_range(size_t(0), DI.size(), rng);
            r->offset.y += DI[dir];
            r->offset.x += DJ[dir];
        }
        else if (ty == 1)
        {
            r->s1 += rand_bool(0.5, rng) ? 0.01 : -0.01;
        }
        else if (ty == 2)
        {
            r->s2 += rand_bool(0.5, rng) ? 0.01 : -0.01;
        }
        else
        {
            r->amp += rand_bool(0.5, rng) ? 1 : -1;
        }
        r->clamp();
        return unique_ptr<Equation>(r);
    }
    unique_ptr<Equation> clone()
    {
        return unique_ptr<Equation>(new SinCos(*this));
    }
};
constexpr const double SinCos::S_MIN;
constexpr const double SinCos::S_MAX;
constexpr const double SinCos::AMP_MIN;
constexpr const double SinCos::AMP_MAX;

struct Xor : Equation {
    Point offset;
    Xor(Point offset) : offset(offset) { }
    double operator()(const Point& p)
    {
        return (p.x - offset.x) ^ (p.y - offset.y);
    }
    void clamp()
    {
        this->offset.x = max(0, min(N, this->offset.x));
        this->offset.y = max(0, min(N, this->offset.y));
    }
    unique_ptr<Equation> delta()
    {
        auto* r = new Xor(*this);
        const size_t dir = rand_range(size_t(0), DI.size(), rng);
        r->offset.y += DI[dir];
        r->offset.x += DJ[dir];
        r->clamp();
        return unique_ptr<Equation>(r);
    }
    unique_ptr<Equation> clone()
    {
        return unique_ptr<Equation>(new Xor(*this));
    }
};

struct XY2 : Equation {
    constexpr const static double R_MIN = 1e-3;
    constexpr const static double R_MAX = 1e-1;
    constexpr const static double AMP_MIN = 10.0;
    constexpr const static double AMP_MAX = 100.0;
    double rx, ry, amp;
    Point offset;
    XY2(Point offset) :
        rx(rand_range(R_MIN, R_MAX, rng)),
        ry(rand_range(R_MIN, R_MAX, rng)),
        amp(rand_range(AMP_MIN, AMP_MAX, rng)),
        offset(offset)
    {
    }
    double operator()(const Point& p)
    {
        double dx = (p.x - offset.x) * (p.x - offset.x) * rx;
        double dy = (p.y - offset.y) * (p.y - offset.y) * ry;
        return amp * exp(-(dx + dy));
    }
    void clamp()
    {
        this->offset.x = max(0, min(N, this->offset.x));
        this->offset.y = max(0, min(N, this->offset.y));
        this->rx = max(R_MIN, min(R_MAX, this->rx));
        this->ry = max(R_MIN, min(R_MAX, this->ry));
        this->amp = max(AMP_MIN, min(AMP_MAX, this->amp));
    }
    unique_ptr<Equation> delta()
    {
        auto* r = new XY2(*this);
        const int ty = rand_range(0, 4, rng);
        if (ty == 0)
        {
            const size_t dir = rand_range(size_t(0), DI.size(), rng);
            r->offset.y += DI[dir];
            r->offset.x += DJ[dir];
        }
        else if (ty == 1)
        {
            r->rx += rand_bool(0.5, rng) ? 0.01 : -0.01;
        }
        else if (ty == 2)
        {
            r->ry += rand_bool(0.5, rng) ? 0.01 : -0.01;
        }
        else
        {
            r->amp += rand_bool(0.5, rng) ? 1 : -1;
        }
        r->clamp();
        return unique_ptr<Equation>(r);
    }
    unique_ptr<Equation> clone()
    {
        return unique_ptr<Equation>(new XY2(*this));
    }
};
constexpr const double XY2::R_MIN;
constexpr const double XY2::R_MAX;
constexpr const double XY2::AMP_MIN;
constexpr const double XY2::AMP_MAX;

template <typename T> vec<unique_ptr<T>> clone_vec(const vec<unique_ptr<T>>& s)
{
    vec<unique_ptr<T>> t;
    for (const auto& e : s)
    {
        t.push_back(unique_ptr<T>(e->clone()));
    }
    return t;
}

// valuesの値を[0,255]に正規化
vec<double> normalize(const vec<double>& values)
{
    assert(not values.empty());
    vec<double> normalized;
    double min_v = *min_element(all(values));
    double max_v = *max_element(all(values));

    forn(i, values.size())
    {
        auto v = min_v == max_v ? 0.0 : (values[i] - min_v) * 255.0 / (max_v - min_v);
        normalized.push_back(v);
    }
    return normalized;
}

double compute_mse(const vec<double>& actual, const vec<double>& predicted)
{
    assert(actual.size() == predicted.size());
    double r = 0.0;
    forn(i, actual.size())
    {
        double d = actual[i] - predicted[i];
        r += d * d;
    }
    return r / (double)actual.size();
}

bool in_grid(int y, int x)
{
    return 0 <= y and y < N and 0 <= x and x < N;
}

struct Solver {
    vec<double> actual;

    Solver()
    {
        cin >> A >> N;
        actual = vec<double>(N * N, -1);
    }

    void solve()
    {
        fprintf(stderr, "start: %lldms\n", as_millis(TIMER.elapsed()));
        int sample_num = min(N / 2, int((N * N / 90) * sqrt(A / 0.2)));
        fprintf(stderr, "sample_num: %d\n", sample_num);

        // サンプル点の選択
        // 既存のサンプル点からの距離が最も大きいもの(タイの場合乱択)を選ぶ
        const int sx = rand_range(1, N - 1, rng);
        const int sy = rand_range(1, N - 1, rng);
        vi min_dist2(N * N, N * N * 4);
        const Point s(sy, sx);
        forn(y, N) forn(x, N)
        {
            const Point p(y, x);
            if (y == 0 or y == N - 1 or x == 0 or x == N - 1)
            {
                min_dist2[p] = -1;
            }
            else
            {
                min_dist2[p] = s.dist2(p);
            }
        }
        vec<Point> sample_points = { s };

        forn(i, sample_num + sample_num / 2 - 1)
        {
            const int best_min_dist2 = *max_element(all(min_dist2));
            vec<Point> candidate;
            forn(y, N) forn(x, N)
            {
                const Point p(y, x);
                if (min_dist2[p] == best_min_dist2)
                {
                    candidate.push_back(p);
                }
            }

            const int pi = rand_range(0, (int)candidate.size(), rng);
            sample_points.push_back(candidate[pi]);

            forn(y, N) forn(x, N)
            {
                chmin(min_dist2[Point(y, x)], Point(y, x).dist2(candidate[pi]));
            }
        }

        vec<Point> known_points;
        vec<bool> known(N * N);
        vec<double> sampled_values;
        auto sample = [&](const Point& p) -> int {
            const int y = p.y;
            const int x = p.x;
            cout << y << " " << x << endl;
            for (int dy = -1; dy <= 1; dy++)
            {
                for (int dx = -1; dx <= 1; dx++)
                {
                    const int ny = y + dy;
                    const int nx = x + dx;
                    const Point np(ny, nx);
                    cin >> actual[np];
                    if (not known[np])
                    {
                        known_points.push_back(np);
                        sampled_values.push_back(actual[np]);
                        known[np] = true;
                    }
                }
            }

            int time;
            cin >> time;
            return time;
        };

        forn(i, sample_num)
        {
            sample(sample_points[i]);
        }

        // サンプルを正規化
        auto sampled_values_norm = normalize(sampled_values);

        const vec<double> equation_weights = { 1.0, 1.0, 1.0, 1.0 };
        auto equation_selector = WeightedIndex<double>(equation_weights);

        // 焼きなましの初期解を乱択で求める
        vec<vec<unique_ptr<Equation>>> best_equations_list(E_MAX + 1);
        vec<double> best_mse_list(E_MAX + 1, TEN(8));
        int turn = 0;
        auto timer = Timer::start();
        while (timer.elapsed() < from_millis(4500))
        {
            turn++;

            int e = rand_range(E_MIN, E_MAX + 1, rng);
            vec<unique_ptr<Equation>> equations;
            forn(i, e)
            {
                const int off_y = rand_range(0, N + 1, rng);
                const int off_x = rand_range(0, N + 1, rng);
                const Point p(off_y, off_x);
                const size_t ei = equation_selector(rng);
                if (ei == 0) equations.emplace_back(unique_ptr<Equation>(new XY2(p)));
                if (ei == 1) equations.emplace_back(unique_ptr<Equation>(new Slope(p)));
                if (ei == 2) equations.emplace_back(unique_ptr<Equation>(new SinCos(p)));
                if (ei == 3) equations.emplace_back(unique_ptr<Equation>(new Xor(p)));
            }

            vec<double> predicted;
            for (auto kp : known_points)
            {
                predicted.push_back(0.0);
                for (const auto& e : equations)
                {
                    predicted.back() += (*e)(kp);
                }
            }

            auto predicted_norm = normalize(predicted);

            auto new_mse = compute_mse(sampled_values_norm, predicted_norm);

            if (new_mse < best_mse_list[e])
            {
                best_equations_list[e] = std::move(equations);
                best_mse_list[e] = new_mse;
            }
        }

        vi index(E_MAX + 1);
        iota(all(index), 0);
        sort(all(index), [&](int i, int j) { return best_mse_list[i] < best_mse_list[j]; });

        // 焼きなまし
        vec<vec<unique_ptr<Equation>>> equations_list;
        vec<double> mse_list;
        int width = 10;
        forn(i, width)
        {
            fprintf(stderr, "choose %d\n", index[i]);
            equations_list.push_back(std::move(best_equations_list[index[i]]));
            mse_list.push_back(best_mse_list[index[i]]);
        }
        best_equations_list.clear();
        best_mse_list = mse_list;
        forn(i, width)
        {
            best_equations_list.push_back(clone_vec(equations_list[i]));
        }

        auto scheduler = Scheduler(5e1, 1e-2, from_millis(4500));
        // パラメータ変更,追加,削除,複数削除
        const auto neighborhood_selector = WeightedIndex<double>({ 3.0, 1.0, 1.0, 0.1 });
        int turn_sa = 0;
        vi transition_count = vi(4);
        vec<vec<double>> predicted(width);
        forn(i, width)
        {
            for (auto kp : known_points)
            {
                predicted[i].push_back(0.0);
                for (const auto& e : equations_list[i])
                {
                    predicted[i].back() += (*e)(kp);
                }
            }
        }

        while (true)
        {
            const double temperature = scheduler.temperature();
            if (temperature < 0.0) break;

            if (width != 1 and scheduler.sw.elapsed() > from_millis(3000))
            {
                auto best_i = min_element(all(best_mse_list)) - best_mse_list.begin();
                swap(best_equations_list[0], best_equations_list[best_i]);
                swap(equations_list[0], equations_list[best_i]);
                swap(best_mse_list[0], best_mse_list[best_i]);
                swap(mse_list[0], mse_list[best_i]);
                swap(predicted[0], predicted[best_i]);
                width = 1;
                fprintf(stderr, "selected mse: %f\n", best_mse_list[0]);

                // 追加のサンプル
                if (best_mse_list[0] >= 30.0)
                {
                    fprintf(stderr, "!additional samples!\n");
                    for (int i = sample_num; i < sample_points.size(); i++)
                    {
                        sample(sample_points[i]);
                    }

                    // sample_values_normの更新
                    sampled_values_norm = normalize(sampled_values);

                    // predictedの更新
                    predicted[0].clear();
                    vec<double> best_predicted;
                    for (auto kp : known_points)
                    {
                        predicted[0].push_back(0.0);
                        for (const auto& e : equations_list[0])
                        {
                            predicted[0].back() += (*e)(kp);
                        }
                        best_predicted.push_back(0.0);
                        for (const auto& e : best_equations_list[0])
                        {
                            best_predicted.back() += (*e)(kp);
                        }
                    }

                    auto predicted_norm = normalize(predicted[0]);
                    mse_list[0] = compute_mse(sampled_values_norm, predicted_norm);
                    auto best_predicted_norm = normalize(best_predicted);
                    best_mse_list[0] = compute_mse(sampled_values_norm, best_predicted_norm);
                    fprintf(stderr, "new mse: %f\n", best_mse_list[0]);
                }
            }

            forn(eli, width)
            {
                turn_sa++;

                const auto ni = neighborhood_selector(rng);

                // パラメータ変更
                if (ni == 0)
                {
                    if (equations_list[eli].empty()) continue;
                    const auto ei = rand_range(0, (int)equations_list[eli].size(), rng);

                    auto new_eq = equations_list[eli][ei]->delta();

                    vec<double> new_predicted = predicted[eli];
                    forn(ki, known_points.size())
                    {
                        const auto kp = known_points[ki];
                        new_predicted[ki] -= (*equations_list[eli][ei])(kp);
                        new_predicted[ki] += (*new_eq)(kp);
                    }

                    auto new_predicted_norm = normalize(new_predicted);

                    auto new_mse = compute_mse(sampled_values_norm, new_predicted_norm);

                    const double delta = new_mse - mse_list[eli];
                    if (rand_bool(transition_probability_min(delta, temperature), rng))
                    {
                        equations_list[eli][ei] = std::move(new_eq);
                        mse_list[eli] = new_mse;
                        predicted[eli] = new_predicted;
                        transition_count[ni]++;
                    }
                }
                // 追加
                else if (ni == 1)
                {
                    if (equations_list[eli].size() >= E_MAX) continue;
                    const auto ei = equation_selector(rng);
                    const auto y = rand_range(0, N + 1, rng);
                    const auto x = rand_range(0, N + 1, rng);
                    const Point offset(y, x);
                    vec<double> new_predicted = predicted[eli];
                    unique_ptr<Equation> new_eq = nullptr;
                    if (ei == 0)
                        new_eq = unique_ptr<Equation>(new XY2(offset));
                    else if (ei == 1)
                        new_eq = unique_ptr<Equation>(new Slope(offset));
                    else if (ei == 2)
                        new_eq = unique_ptr<Equation>(new SinCos(offset));
                    else
                        new_eq = unique_ptr<Equation>(new Xor(offset));

                    forn(ki, known_points.size())
                    {
                        new_predicted[ki] += (*new_eq)(known_points[ki]);
                    }

                    auto new_predicted_norm = normalize(new_predicted);

                    auto new_mse = compute_mse(sampled_values_norm, new_predicted_norm);

                    const double delta = new_mse - mse_list[eli];
                    if (rand_bool(transition_probability_min(delta, temperature), rng))
                    {
                        equations_list[eli].push_back(std::move(new_eq));
                        mse_list[eli] = new_mse;
                        predicted[eli] = new_predicted;
                        transition_count[ni]++;
                    }
                }
                // 削除
                else if (ni == 2)
                {
                    if (equations_list[eli].size() <= E_MIN) continue;

                    const auto ei = rand_range(size_t(0), equations_list[eli].size(), rng);

                    vec<double> new_predicted = predicted[eli];

                    forn(ki, known_points.size())
                    {
                        new_predicted[ki] -= (*equations_list[eli][ei])(known_points[ki]);
                    }

                    auto new_predicted_norm = normalize(new_predicted);

                    auto new_mse = compute_mse(sampled_values_norm, new_predicted_norm);

                    const double delta = new_mse - mse_list[eli];
                    if (rand_bool(transition_probability_min(delta, temperature), rng))
                    {
                        swap_remove(equations_list[eli], ei);
                        mse_list[eli] = new_mse;
                        predicted[eli] = new_predicted;
                        transition_count[ni]++;
                    }
                }
                // 複数削除
                else
                {
                    if (equations_list[eli].size() < 3) continue;
                    const int k = equations_list[eli].size() / 3;
                    set<size_t> erased;
                    // 誕パラしそう
                    forn(i, k)
                    {
                        erased.insert(rand_range(size_t(0), equations_list[eli].size(), rng));
                    }

                    vec<double> new_predicted = predicted[eli];

                    forn(ki, known_points.size())
                    {
                        for (const auto ei : erased)
                        {
                            new_predicted[ki] -= (*equations_list[eli][ei])(known_points[ki]);
                        }
                    }

                    auto new_predicted_norm = normalize(new_predicted);

                    auto new_mse = compute_mse(sampled_values_norm, new_predicted_norm);

                    const double delta = new_mse - mse_list[eli];
                    if (rand_bool(transition_probability_min(delta, temperature), rng))
                    {
                        vec<unique_ptr<Equation>> new_equations;
                        forn(i, equations_list[eli].size())
                        {
                            if (not erased.count(i))
                            {
                                new_equations.push_back(std::move(equations_list[eli][i]));
                            }
                        }
                        equations_list[eli] = std::move(new_equations);
                        mse_list[eli] = new_mse;
                        predicted[eli] = new_predicted;
                        transition_count[ni]++;
                    }
                }

                if (mse_list[eli] < best_mse_list[eli])
                {
                    best_mse_list[eli] = mse_list[eli];
                    best_equations_list[eli] = clone_vec(equations_list[eli]);
                }
            }
        }

        cout << "done" << endl;

        fprintf(stderr, "turn: %d\n", turn);
        fprintf(stderr, "sample mse: %f\n", best_mse_list[0]);
        fprintf(stderr, "# of equations: %zd\n", best_equations_list[0].size());
        fprintf(stderr, "turn_sa: %d\n", turn_sa);
        fprintf(stderr, "transition_count: %d\n", accumulate(all(transition_count), 0));
        forn(i, transition_count.size())
        {
            fprintf(stderr, "transition_count[%d]: %d\n", i, transition_count[i]);
        }

        vec<double> ans(N * N);
        forn(y, N)
        {
            forn(x, N)
            {
                const Point p(y, x);
                for (const auto& e : best_equations_list[0])
                {
                    ans[p] += (*e)(p);
                }
            }
        }

        const double min_v = *min_element(all(ans));
        const double max_v = *max_element(all(ans));
        forn(y, N)
        {
            forn(x, N)
            {
                const Point p(y, x);
                if (actual[p] >= -0.1)
                {
                    cout << int(actual[p]) << endl;
                }
                else
                {
                    cout << int(min_v == max_v ? 0.0 : (ans[p] - min_v) * 255 / (max_v - min_v)) << endl;
                }
            }
        }

        cout.flush();
    }
};

int main()
{
    fastio();
    Solver().solve();
    fprintf(stderr, "elapsed: %lldms\n", as_millis(TIMER.elapsed()));
    return 0;
}
