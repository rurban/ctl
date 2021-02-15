#include <algorithm>
#include <array>
#include <deque>
#include <list>
#include <queue>
#include <set>
#include <stack>
#include <string>
#include <unordered_set>
#include <vector>

#define N 1024

void A()
{
    std::deque<int> a;
    std::vector<int> b;
    std::list<int> c;
    std::queue<int> d;
    std::set<int> e;
    std::stack<int> f;
    std::string g;
    std::priority_queue<int> i;
    std::array<int, N> j;
    std::unordered_set<int> k;

    for (int el = 0; el < N; el++)
    {
        a.push_back(el);
        a.push_front(el);
        b.push_back(el);
        c.push_back(el);
        c.push_front(el);
        d.push(el);
        e.insert(el);
        f.push(el);
        g.push_back('A' + el);
        i.push(el);
        j[el] = el;
        k.insert(el);
    }

    a.pop_back();
    a.pop_front();
    b.pop_back();
    c.pop_back();
    c.pop_front();
    d.pop();
    e.erase(1);
    f.pop();
    g.pop_back();
    i.pop();
    j[0] = 0;
    k.erase(1);

    sort(a.begin(), a.end());
    std::count(a.begin(), a.end(), 0);
    sort(b.begin(), b.end());
    std::count(b.begin(), b.end(), 0);
    c.sort();
    std::count(c.begin(), c.end(), 0);
    std::count(e.begin(), e.end(), 0);
    std::sort(g.begin(), g.end());
    std::count(g.begin(), g.end(), 'A');
    std::sort(j.begin(), j.end());
    std::count(j.begin(), j.end(), 0);
    std::count(k.begin(), k.end(), 0);
}

void B()
{
    std::deque<short> a;
    std::vector<short> b;
    std::list<short> c;
    std::queue<short> d;
    std::set<short> e;
    std::stack<short> f;
    std::string g;
    std::priority_queue<short> i;

    a.push_back(1);
    a.push_front(1);
    b.push_back(1);
    c.push_back(1);
    c.push_front(1);
    d.push(1);
    e.insert(1);
    f.push(1);
    i.push(1);

    a.pop_back();
    a.pop_front();
    b.pop_back();
    c.pop_back();
    c.pop_front();
    d.pop();
    e.erase(1);
    f.pop();
    i.pop();
}

void C()
{
    std::deque<float> a;
    std::vector<float> b;
    std::list<float> c;
    std::queue<float> d;
    std::set<float> e;
    std::stack<float> f;
    std::string g;
    std::priority_queue<float> i;

    a.push_back(1.0);
    a.push_front(1.0);
    b.push_back(1.0);
    c.push_back(1.0);
    c.push_front(1.0);
    d.push(1.0);
    e.insert(1.0);
    f.push(1.0);
    i.push(1.0);

    a.pop_back();
    a.pop_front();
    b.pop_back();
    c.pop_back();
    c.pop_front();
    d.pop();
    e.erase(1.0);
    f.pop();
    i.pop();
}

void D()
{
    std::deque<double> a;
    std::vector<double> b;
    std::list<double> c;
    std::queue<double> d;
    std::set<double> e;
    std::stack<double> f;
    std::string g;
    std::priority_queue<double> i;

    a.push_back(1.0);
    a.push_front(1.0);
    b.push_back(1.0);
    c.push_back(1.0);
    c.push_front(1.0);
    d.push(1.0);
    e.insert(1.0);
    f.push(1.0);
    i.push(1.0);

    a.pop_back();
    a.pop_front();
    b.pop_back();
    c.pop_back();
    c.pop_front();
    d.pop();
    e.erase(1.0);
    f.pop();
    i.pop();
}

int main()
{
    A();
    B();
    C();
    D();
}
