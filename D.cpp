#include <iostream>
#include <limits>
#include <vector>
#include <cassert>
#include <sstream>
#include <variant>
#include <list>
#include <utility>
#include <string>

typedef unsigned long long ull;
typedef long long ll;

using namespace std;

template <class T> class GroupElement;

template <class T>
class GroupOps {
public:
    typedef T Type;
    typedef GroupElement<GroupOps<T>> Elem;
    virtual T one() const = 0;
    virtual T add(const T &a, const T &b) const = 0;
    virtual T inverse(const T &a) const = 0;
    virtual Elem create(const T &a) const = 0;

    Elem create() const {
        return create(one());
    }
    virtual ~GroupOps() {};
};

template <class Ops>
struct GroupElement {
    typedef typename Ops::Type T;
    typedef GroupElement<Ops> Elem;
    T elem;
    const Ops *ops;
    GroupElement(const Ops *_ops): elem(_ops->one()), ops(_ops) { }
    GroupElement(const Ops *_ops, const T &_elem): elem(_elem), ops(_ops) { }
    Elem operator*(const Elem &other) const {
        return Elem(ops, ops->add(this->elem, other.elem));
    }
    Elem operator/(const Elem &other) const {
        return Elem(ops, ops->minus(this->elem, other.elem));
    }
    Elem inverse() const {
        return ops->create(ops->inverse(this->elem));
    }
    T get() const {
        return elem;
    }
};

template <class Ops>
istream& operator>>(istream &in, GroupElement<Ops> &elem) {
    return in >> elem.elem;
}
template <class Ops>
ostream& operator<<(istream &out, GroupElement<Ops> &elem) {
    return out << elem.elem;
}

template <class T> class FieldElement;

template <class T>
class FieldOps {
public:
    typedef T Type;
    typedef FieldElement<FieldOps<T>> Elem;
    virtual T zero() const = 0;
    virtual T one() const = 0;
    virtual T add(const T &a, const T &b) const = 0;
    virtual T multiply(const T &a, const T &b) const = 0;
    virtual T minus(const T &a) const = 0;
    virtual T inverse(const T &a) const = 0;
    virtual Elem create(const T &a) const = 0;

    Elem create() const {
        return create(zero());
    }
    virtual ~FieldOps() {};
};

template <class Ops>
struct FieldElement {
    typedef typename Ops::Type T;
    typedef FieldElement<FieldOps<T>> Elem;
    typedef Ops Field;
    T elem;
    const Ops *ops;
    FieldElement(const Ops *_ops): elem(_ops->zero()), ops(_ops) { }
    FieldElement(const Ops *_ops, const T &_elem): elem(_elem), ops(_ops) { }
    Elem operator+(const Elem &other) const {
        return Elem(ops, ops->add(this->elem, other.elem));
    }
    Elem operator-() const {
        return Elem(ops, ops->minus(this->elem));
    }
    Elem operator-(const Elem &other) const {
        return Elem(ops, ops->add(this->elem, ops->minus(other.elem)));
    }
    Elem operator*(const Elem &other) const {
        return Elem(ops, ops->multiply(this->elem, other.elem));
    }
    Elem operator/(const Elem &other) const {
        return Elem(ops, ops->multiply(this->elem, ops->inverse(other.elem)));
    }
    Elem inverse() const {
        return ops->create(ops->inverse(this->elem));
    }
    T get() const {
        return elem;
    }
};
template <class Ops>
istream& operator>>(istream &in, FieldElement<Ops> &elem) {
    return in >> elem.elem;
}
template <class Ops>
ostream& operator<<(ostream &out, const FieldElement<Ops> &elem) {
    return out << elem.elem;
}

template <class T>
T pow(T x, ull n) {
    //cout << "! " << n << '\n';
    if (n == 0)
        return x.ops->create(x.ops->one());
    if (n % 2 == 0) {
        T x2 = x * x;
        T ppow = pow(x2, n / 2);
        return ppow;
    }
    else
        return pow(x, n - 1) * x;
}

// --------- Eulliptic curves ---------

template <class K>
class Point2 {
    K x, y;
    Point2(K x, K y): x(x), y(y) {}
};

class EInf {};

template <class K>
class EPoint2 {
    std::variant<Point2<K>, EInf> elem;
    EPoint2() {
        elem = EInf();
    }
    EPoint2(K x, K y) {
        elem = Point2<K>(x, y);
    }
    bool is_inf() const {
        return holds_alternative<EInf>(elem);
    }
    K x() const {
        return get<Point2<K>>(elem).x;
    }
    K y() const {
        return get<Point2<K>>(elem).y;
    }
};



template<class K>
class EullipticCurveOps: public GroupOps<EPoint2<K>> {
    K a, b;
    EullipticCurveOps(K a, K b): a(a), b(b) {
        assert(4 * a * a * a + 27 * b * b != 0);
    }
    EPoint2<K> one() {
        return EPoint2<K>();
    }
    EPoint2<K> add(const EPoint2<K> &a, const EPoint2<K> &b) {
        if (a.is_inf())
            return b;
        if (b.is_inf())
            return a;
        if (a.x() == b.x() && a.y() != b.y())
            return EPoint2<K>();
        K k;
        if (a.x() == b.x())
            k = (3 * a.x() * a.x() + this->a) / (2 * a.y());
        else
            k = (b.y() - a.y()) / (b.x() - a.x());
        K x3 = k * k - a.x() - b.x();
        K y3 = k * (x3 - a.x()) + a.y();
        return EPoint2<K>(x3, y3);
    }
    EPoint2<K> inverse(const EPoint2<K> &a) {
        if (a.is_inf())
            return a;
        EPoint2<K> b = a;
        b.y = -b.y;
        return b;
    }
    typename EullipticCurveOps::Elem create(const EPoint2<K> &a) {
        if (a.is_inf())
            return EullipticCurveOps::Elem(this, a);
        assert(a.y() * a.y() == a.x() * a.x() * a.x() + a.x() * this->a + this->b);
        return EullipticCurveOps::Elem(this, a);
    }
};


// --------- Multiplicative Modulo group ---------
pair<ll, ll> operator_div(const ll &a, const ll &b) {
    return {a / b, a % b};
}

ll gcd(const ll &a, const ll &b, ll &x, ll &y) {
    if (a == 0) {
        x = 0;
        y = 1;
        return b;
    }
    ll x1, y1;
    auto [q, r] = operator_div(b, a);
    ll g = gcd(r, a, x1, y1);
    x = y1 - q * x1;
    y = x1;
    return g;
}

class ModuloOps: public FieldOps<ull> {
public:
    ull MOD;
    ModuloOps(ull MOD): MOD(MOD) {}
    ull zero() const override {
        return 0;
    }
    ull one() const override {
        return 1;
    }
    ull add(const ull &a, const ull &b) const override {
        return (a + b) % MOD;
    }
    ull multiply(const ull &a, const ull &b) const override {
        return (a * b) % MOD;
    }
    ull minus(const ull &a) const override {
        return (MOD - a) % MOD;
    }
    ull inverse(const ull &a) const override {
        ll x, y, mod = MOD;
        gcd(a, MOD, x, y);
        x = ((x % mod) + mod) % mod;
        return x;
    }
    typename ModuloOps::Elem create(const ull &a) const override {
        return ModuloOps::Elem(this, a % MOD);
    }
};

int char_to_number(char symbol) {
  if (symbol >= 48 && symbol <= 57)
    return symbol - 48;
  if (symbol >= 65 && symbol <= 90)
    return symbol - 55;
  if (symbol >= 97 && symbol <= 122)
    return symbol - 61;
  if (symbol == 32)
    return 62;
  if (symbol == 46)
    return 63;
  return 64;
}

char number_to_char(int num) {
    if (num >= 0 && num <= 9)
        return num + 48;
    if (num >= 10 && num <= 35)
        return num + 55;
    if (num >= 36 && num <= 61)
        return num + 61;
    if (num == 62)
        return 32;
    if (num == 63)
        return 46;
    return -1;
}

class BigInt {
public:
    list<ull> d;
    ull MOD;
    BigInt(list<ull> d, ull MOD): d(d), MOD(MOD) {};
    BigInt(ull d, ull MOD): MOD(MOD) {
        assert(d < MOD);
        if (d > 0)
            this->d = {d};
    };
    BigInt(ull MOD): MOD(MOD) {}
};

BigInt operator+(const BigInt &a, const BigInt &b) {
    assert(a.MOD == b.MOD);
    ull mod = a.MOD;
    list<ull> target;
    ull remainder = 0;
    list<ull>::const_iterator a_iter = a.d.begin(), b_iter = b.d.begin();
    while (true) {
        ull cur_value = remainder;
        if (a_iter != a.d.end())
            cur_value += *a_iter++;
        if (b_iter != b.d.end())
            cur_value += *b_iter++;
        if (cur_value == 0 && a_iter == a.d.end() && b_iter == b.d.end())
            break;
        target.push_back(cur_value % mod);
        remainder = cur_value / mod;
    }
    return {target, mod};
}

ull bigint_div(BigInt &c, ull b) {
    ull mod = c.MOD;
    ull remainder = 0;
    if (c.d.empty())
        return 0;
    for (auto it = c.d.rbegin(); it != c.d.rend();++it) {
        ull cur_value = *it + remainder * mod;
        *it = cur_value / b;
        remainder = cur_value % b;
    }
    while (!c.d.empty() && *c.d.rbegin() == 0)
        c.d.erase(prev(c.d.end()));
    return remainder;
}

BigInt operator<<(const BigInt &a, unsigned int s) {
    if (a.d.empty())
        return BigInt(a.MOD);
    BigInt b = a;
    for (int i = 0; i < s; ++i)
        b.d.push_front(0);
    return b;
}
BigInt operator*(const BigInt &a, ull b) {
    assert(b < a.MOD);
    ull mod = a.MOD;
    list<ull> target;
    ull remainder = 0;
    list<ull>::const_iterator a_iter = a.d.begin();
    while (true) {
        ull cur_value = remainder;
        if (a_iter != a.d.end())
            cur_value += *a_iter++ * b;
        if (cur_value == 0 && a_iter == a.d.end())
            break;
        target.push_back(cur_value % mod);
        remainder = cur_value / mod;
    }
    return {target, mod};
}

BigInt operator*(const BigInt &a, const BigInt &b) {
    assert(a.MOD == b.MOD);
    ull mod = a.MOD;
    BigInt res(mod);
    int i = 0;
    for (ull ax : a.d) {
        res = res + ((b * ax) << i);
        ++i;
    }
    return res;
}

BigInt convert(const BigInt &a, ull MOD) {
    list<ull> target;
    BigInt b = a;
    while (!b.d.empty()) {
        ull res = bigint_div(b, MOD);
        target.push_back(res);
    }
    return {target, MOD};
}

template <class FElem>
class Poly {
public:
    list<FElem> d;
    Poly(list<FElem> _d): d(_d) {
        while (!d.empty() && d.rbegin()->elem == d.rbegin()->ops->zero())
            d.erase(prev(d.end()));
    }
    Poly(){}
    Poly(FElem x) {
        if (x.get() != x.ops->zero())
            d.push_back(x);
    }
    size_t size() const {
        return d.size();
    }
    bool empty() const {
        return d.empty();
    }
};

template <class FElem>
Poly<FElem> operator*(const Poly<FElem> &a, const Poly<FElem> &b) {
    if (a.empty() || b.empty())
        return {};
    auto *ops = !a.empty() ? b.d.begin()->ops : a.d.begin()->ops;
    vector<FElem> target(a.size() + b.size() - 1, ops->create(ops->zero()));
    int ai = 0;
    for (FElem ax : a.d) {
        int bi = 0;
        for (FElem bx : b.d) {
            target[ai + bi] = target[ai + bi] + ax * bx;
            bi++;
        }
        ++ai;
    }
    list<FElem> p(target.begin(), target.end());
    Poly<FElem> pp(p);
    return pp;
}

template <class FElem>
Poly<FElem> operator+(const Poly<FElem> &a, const Poly<FElem> &b)  {
    if (a.empty())
        return b;
    if (b.empty())
        return a;
    auto *ops = a.d.begin()->ops;
    list<FElem> target;
    auto a_iter = a.d.begin(), b_iter = b.d.begin();
    while (true) {
        FElem cur_value = ops->create(ops->zero());
        if (a_iter != a.d.end())
            cur_value = cur_value + *a_iter++;
        if (b_iter != b.d.end())
            cur_value = cur_value + *b_iter++;
        if (cur_value.elem == ops->zero() && a_iter == a.d.end() && b_iter == b.d.end())
            break;
        target.push_back(cur_value);
    }
    return target;
}
template <class FElem>
Poly<FElem> operator-(const Poly<FElem> &a)  {
    Poly<FElem> b = a;
    for (auto it = b.d.begin(); it != b.d.end(); ++it)
        *it = -*it;
    return b;
}
template <class FElem>
Poly<FElem> operator-(const Poly<FElem> &a, const Poly<FElem> &b)  {
    return a + (-b);
}

template <class FElem>
FElem _poly_div_helper(Poly<FElem> &a, const Poly<FElem> &b) {
    if (a.size() < b.size())
        return b.d.begin()->ops->create(b.d.begin()->ops->zero());
    FElem mult = a.d.back() / b.d.back();
    auto a_iter = a.d.rbegin();
    auto b_iter = b.d.rbegin();
    while (b_iter != b.d.rend()) {
        *a_iter = *a_iter - *b_iter * mult;
        ++a_iter, ++b_iter;
    }
    while (!a.empty() && a.d.rbegin()->elem == a.d.begin()->ops->zero())
        a.d.erase(prev(a.d.end()));
    return mult;
}

template <class F>
pair<Poly<FieldElement<F>>, Poly<FieldElement<F>>> operator_div(const Poly<FieldElement<F>> &a, const Poly<FieldElement<F>> &b) {
    if (a.size() < b.size())
        return {{}, a};
    if (a.empty())
        return {{}, {}};
    auto *ops = a.d.begin()->ops;
    vector<FieldElement<F>> res(a.size() - b.size() + 1, ops->create(ops->zero()));
    Poly<FieldElement<F>> c = a;
    while (c.size() >= b.size()) {
        int i = c.size() - b.size();
        FieldElement<F> x = _poly_div_helper(c, b);
        res[i] = x;
    }
    list<FieldElement<F>> p(res.begin(), res.end());
    Poly<FieldElement<F>> pp(p);
    return {pp, c};
}
template <class FElem>
Poly<FElem> gcd(const Poly<FElem> &a, const Poly<FElem> &b, Poly<FElem> &x, Poly<FElem> &y) {
    if (a.empty()) {
        auto *ops = b.d.begin()->ops;
        x = {};
        y = {ops->create(ops->one())};
        return b;
    }
    auto *ops = a.d.begin()->ops;
    Poly<FElem> x1, y1;
    auto [q, r] = operator_div(b, a);
    Poly<FElem> g = gcd(r, a, x1, y1);
    x = y1 - q * x1;
    y = x1;
    return g;
}

template <class FElem>
class PolyOps: public FieldOps<Poly<FElem>> {
public:
    typedef typename FElem::Field Ops;
    typedef Poly<FElem> P;
    const Ops *ops;
    Poly<FElem> f;
    PolyOps(const Ops *ops, Poly<FElem> f): ops(ops), f(f) {}
    Poly<FElem> zero() const override {
        return {};
    }
    Poly<FElem> one() const override {
        return {ops->create(ops->one())};
    }
    Poly<FElem> add(const Poly<FElem> &a, const Poly<FElem> &b) const override {
        list<FElem> target;
        auto a_iter = a.d.begin(), b_iter = b.d.begin();
        while (true) {
            FElem cur_value = 0;
            if (a_iter != a.d.end())
                cur_value = cur_value + *a_iter++;
            if (b_iter != b.d.end())
                cur_value = cur_value + *b_iter++;
            if (cur_value.elem == ops->zero() && a_iter == a.d.end() && b_iter == b.d.end())
                break;
            target.push_back(cur_value);
        }
        return {target};
    }
    Poly<FElem> multiply(const Poly<FElem> &a, const Poly<FElem> &b) const override {
        auto ab = a * b;
        auto res = operator_div(ab, f);
        return res.second;
    }
    Poly<FElem> minus(const Poly<FElem> &a) const override {
        Poly<FElem> c = a;
        for (auto it = c.d.begin(); it != c.d.end(); ++it)
            *it = -*it;
        return c;
    }
    Poly<FElem> inverse(const Poly<FElem> &a) const override {
        Poly<FElem> x, y;
        auto g = gcd(a, f, x, y);
        assert(g.size() == 1);
        auto newx = x * Poly<FElem>(g.d.begin()->inverse());
        return newx;
    }
    typename PolyOps<FElem>::Elem create(const Poly<FElem> &a) const override {
        Poly<FElem> c = a;
        while (!c.empty() && c.d.rbegin()->elem == ops->zero())
            c.d.erase(prev(c.d.end()));
        return typename PolyOps<FElem>::Elem(this, operator_div(c, f).second);
    }
};

template <class Ops>
class ElGamalEncryptionSystem {
public:
    typedef typename Ops::Type T;
    typedef typename Ops::Elem Elem;
    Ops *ops;
    Elem g;
    ull p;
    ElGamalEncryptionSystem(Ops *ops, ull p, T g): ops(ops), p(p), g(ops->create(g)) {}
    ElGamalEncryptionSystem(Ops *ops, ull p): ops(ops), p(p), g(ops->create(ops->one())) {}
    pair<T, T> encrypt(T message, T pub) {
        ull b = rand() % (p - 1) + 1;
        Elem pubb = pow(ops->create(pub), b);

        Elem encrypted = ops->create(message) * pubb;
        Elem gb = pow(g, b);
        return {encrypted.get(), gb.get()};
    }
    T decrypt(T enc, T b, ull priv) {
        Elem genc = ops->create(enc);
        Elem gab = pow(ops->create(b), priv);
        Elem antisalt = gab.inverse();
        Elem decrypted = genc * antisalt;
        return decrypted.get();
    }
};

bool input_poly(istream &in, const ModuloOps *ops, Poly<typename ModuloOps::Elem> &f) {
    f.d.clear();
    string fs;
    if (!getline(cin, fs))
        return false;
    stringstream fss(fs);
    ll x;
    while (fss >> x) {
        x = (x + ops->MOD) % ops->MOD;
        f.d.push_back(ops->create(x));
    }
    return true;
}

template <class T>
void output_poly(ostream &out, const Poly<T> &p) {
    for (auto x : p.d)
        out << x << ' ';
    out << '\n';
}

int main(int argc, char *argv[]) {
    ull p;
    cin >> p;
    cin.ignore (numeric_limits<streamsize>::max(), '\n' ); 
    ModuloOps G(p);
    Poly<ModuloOps::Elem> f;
    input_poly(cin, &G, f);
    ull k;
    cin >> k;
    cin.ignore (numeric_limits<streamsize>::max(), '\n' ); 

    PolyOps<ModuloOps::Elem> polyops(&G, f);

    ElGamalEncryptionSystem<PolyOps<ModuloOps::Elem>> enc(&polyops, p);

    list<ull> res;
    Poly<ModuloOps::Elem> gb, m;
    while (input_poly(cin, &G, gb) && input_poly(cin, &G, m)) {
        auto h = enc.decrypt(m, gb, k);
        for (auto x : h.d)
            res.push_back(x.get());
    }
    BigInt bs(res, p);
    bs = convert(bs, 64);
    for (int x: bs.d)
        cout << number_to_char(x);
    cout << '\n';
}
