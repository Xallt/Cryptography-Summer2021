#include <iostream>
#include <vector>
#include <cassert>
#include <variant>
#include <list>
#include <utility>
#include <string>

typedef unsigned long long ull;
typedef long long ll;

using namespace std;

template <class T> class GroupOps;
template <class T> class Element;

template <class T>
class GroupOps {
public:
    typedef T Type;
    typedef Element<T> Elem;
    virtual T id() const = 0;
    virtual T add(const T &a, const T &b) const = 0;
    virtual T inverse(const T &a) const = 0;
    T minus(const T &a, const T &b) const {
        return this->add(a, this->inverse(b));
    }

    Elem create() {
        return Element<T>(this, id());
    }
    Elem create(const T &a) {
        return Element<T>(this, a);
    }
    virtual ~GroupOps() {};
};

template <class T>
struct Element {
    T elem;
    GroupOps<T> *ops;
    Element(GroupOps<T> *_ops): elem(_ops->id()), ops(_ops) { }
    Element(GroupOps<T> *_ops, const T &_elem): elem(_elem), ops(_ops) { }
    Element<T> operator*(const Element<T> &other) const {
        T other_elem = other.elem;
        T this_elem = this->elem;
        T addition = ops->add(this_elem, other_elem);
        return Element(ops, addition);
    }
    Element<T> operator-() const {
        return Element(ops, ops->inverse(this->elem));
    }
    Element<T> operator/(const Element<T> &other) const {
        return Element(ops, ops->minus(this->elem, other.elem));
    }
    Element<T> inverse() const {
        return ops->create(ops->inverse(this->elem));
    }
    T get() const {
        return elem;
    }
};

template <class T>
T pow(T x, ull n) {
    if (n == 0)
        return T(x.ops);
    if (n % 2 == 0)
        return pow(x * x, n / 2);
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
    EPoint2<K> id() {
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
};


// --------- Multiplicative Modulo group ---------

ll _inverse_helper(ll a, ll b, ll &x, ll &y) {
    if (a == 0) {
        x = 0;
        y = 1;
        return b;
    }
    ll x1, y1;
    ll g = _inverse_helper(b % a, a, x1, y1);
    x = y1 - (b / a) * x1;
    y = x1;
    return g;
}

class MultiplicativeModuloOps: public GroupOps<ull> {
public:
    ull MOD;
    MultiplicativeModuloOps(ull MOD): MOD(MOD) {}
    ull id() const override {
        return 1;
    }
    ull add(const ull &a, const ull &b) const override {
        return a * b % MOD;
    }
    ull inverse(const ull &a) const override {
        //cout << "Inverting " << a << " by " << MOD << '\n';
        ll x, y, mod = MOD;
        _inverse_helper(a, MOD, x, y);
        x = ((x % mod) + mod) % mod;
        return x;
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

template <class Ops>
class ElGamalEncryptionSystem {
public:
    typedef typename Ops::Type T;
    typedef typename Ops::Elem Elem;
    Ops *ops;
    Elem g;
    ull p;
    ElGamalEncryptionSystem(Ops *ops, ull p, T g): ops(ops), p(p), g(ops->create(g)) {}
    ElGamalEncryptionSystem(Ops *ops, ull p): ops(ops), p(p), g(ops->create(ops->id())) {}
    pair<T, T> encrypt(T message, T pub) {
        ull salt = rand() % (p - 1) + 1;
        Elem decrypted = ops->create(message) * pow(ops->create(pub), salt);
        Elem b = pow(g, salt);
        return {decrypted.get(), b.get()};
    }
    T decrypt(T enc, T b, ull priv) {
        Elem genc = ops->create(enc);
        Elem gab = pow(ops->create(b), priv);
        Elem antisalt = pow(ops->create(b), priv).inverse();
        //cout << genc.get() << ' ' << gab.get() << ' ' << antisalt.get() << '\n';
        return (genc * antisalt).get();
    }
};

int main(int argc, char *argv[]) {
    ull p, k;
    cin >> p >> k;

    MultiplicativeModuloOps G(p);
    ElGamalEncryptionSystem<MultiplicativeModuloOps> enc(&G, p);

    ull m, b;
    list<ull> target;
    while (cin >> b >> m) {
        ull dec = enc.decrypt(m, b, k);
        target.push_back(dec);
    }
    BigInt bs(target, p);
    bs = convert(bs, 64);
    for (int x : bs.d) {
        cout << number_to_char(x);
    }
    cout << '\n';

    return 0;
}
