#include <iostream>
#include <algorithm>
#include <array>
#include <cassert>
#include <bitset>
#include <cmath>
#include <complex>
#include <cstdint>
#include <deque>
#include <functional>
#include <iomanip>
#include <limits>
#include <list>
#include <map>
#include <numeric>
#include <queue>
#include <random>
#include <set>
#include <stack>
#include <string>
#include <tuple>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include <cctype>


using namespace std;

using ll = long long;
using ull = unsigned long long;
using ld = long double;
using i128 = __int128_t;
using u128 = __uint128_t;

using pii = pair<int,int>;
using pll = pair<ll,ll>;
using tiii = tuple<int,int,int>;
using tiill = tuple<int,int,ll>;

template<class T> using v = vector<T>;
using vi = vector<int>;
using vl = vector<ll>;
using vd = vector<double>;
using vpii = vector<pii>;
using vc = vector<char>;
using vs = vector<string>;
using vb = vector<bool>;
using vvi = vector<vi>;
using vvl = vector<vl>;
using vvb = vector<vb>;
using vvs = vector<vs>;
using vvpii = vector<vpii>;
using Graph = vector<vector<int>>;

constexpr int INF = 1000000000;
constexpr ll LINF = (1LL << 62);
constexpr int MOD = 998244353;
constexpr int MOD1 = 1000000007;
constexpr ld EPS = 1e-12;
constexpr ld PI = 3.141592653589793238462643383279502884L;

constexpr int dx4[] = {1,0,-1,0};
constexpr int dy4[] = {0,1,0,-1};
constexpr int dx8[] = {1,1,1,0,0,-1,-1,-1};
constexpr int dy8[] = {1,0,-1,1,-1,1,0,-1};
vi digit = {0,1,2,3,4,5,6,7,8,9};
vl primes = {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97};

#define rep(i,n) for(int i=0;i<(int)(n);i++)
#define rrep(i,n) for(int i=(int)(n)-1;i>=0;i--)
#define reps(i,s,n) for(int i=(s);i<(int)(n);i++)
#define rreps(i,s,n) for (int i=(int)(s)-1; i >= (int)(n); i--)
#define each(x,a) for(auto&& x:(a))
#define eachs(x,y,a,i) for (auto& [x,y]:a[i])
#define all(x) (x).begin(),(x).end()
#define rall(x) (x).rbegin(),(x).rend()

template<class T>
bool chmin(T& a,const T& b){
    if(a>b){
        a=b;
        return true;
    }
    return false;
}

template<class T>
bool chmax(T& a,const T& b){
    if(a<b){
        a=b;
        return true;
    }
    return false;
}

template<class T>
void read(T& x){
    cin>>x;
}

template<class T,class... Ts>
void read(T& x,Ts&... xs){
    cin>>x;
    read(xs...);
}

template<class T>
void read(vector<T>& a){
    for(auto& x:a) cin>>x;
}

template<class T>
void print(const T& x){
    cout<<x<<'\n';
}

template<class T>
void print(const vector<T>& a){
    rep(i,a.size()){
        if(i) cout<<' ';
        cout<<a[i];
    }
    cout<<'\n';
}

template<class T>
ll sum(const vector<T>& a){
    return accumulate(all(a),0LL);
}

template<class T>
T min_value(const vector<T>& a){
    return *min_element(all(a));
}

template<class T>
T max_value(const vector<T>& a){
    return *max_element(all(a));
}

ll power(ll base, ll exp) {
    ll res = 1;
    while (exp > 0) {
        if (exp & 1) res *= base;
        base *= base;
        exp >>= 1;
    }
    return res;
}


template<class T>
vector<T> prefix_sum(const vector<T>& a){
    vector<T> s(a.size()+1);
    rep(i,a.size()) s[i+1]=s[i]+a[i];
    return s;
}

template<class T>
vector<T> compress(vector<T> a){
    sort(all(a));
    a.erase(unique(all(a)),a.end());
    return a;
}

template<class T>
int lower_bound_index(const vector<T>& a,const T& x){
    return lower_bound(all(a),x)-a.begin();
}

template<class T>
int upper_bound_index(const vector<T>& a,const T& x){
    return upper_bound(all(a),x)-a.begin();
}

template<class F>
long long binary_search_ll(long long ok,long long ng,F f){
    while(abs(ok-ng)>1){
        long long mid=(ok+ng)/2;
        if(f(mid)) ok=mid;
        else ng=mid;
    }
    return ok;
}

template<class F>
double binary_search_double(double ok,double ng,F f,int iter=100){
    rep(_,iter){
        double mid=(ok+ng)/2;
        if(f(mid)) ok=mid;
        else ng=mid;
    }
    return ok;
}

void Yes(bool x=true){
    cout<<(x?"Yes":"No")<<'\n';
}

void No(bool x=true){
    cout<<(x?"No":"Yes")<<'\n';
}

ll mod_pow(ll a,ll n,ll mod){
    ll r=1;
    while(n){
        if(n&1) r=(i128)r*a%mod;
        a=(i128)a*a%mod;
        n>>=1;
    }
    return r;
}

ll mod_inv(ll a,ll mod){
    return mod_pow(a,mod-2,mod);
}

ll extgcd(ll a,ll b,ll& x,ll& y){
    if(b==0){
        x=1;
        y=0;
        return a;
    }
    ll x2,y2;
    ll g=extgcd(b,a%b,x2,y2);
    x=y2;
    y=x2-(a/b)*y2;
    return g;
}

ll mod_inv_extgcd(ll a,ll mod){
    ll x,y;
    extgcd(a,mod,x,y);
    x%=mod;
    if(x<0) x+=mod;
    return x;
}

vector<pair<ll,int>> prime_factorization(ll n){
    vector<pair<ll,int>> res;
    for(ll p=2;p*p<=n;p+=(p==2?1:2)){
        if(n%p) continue;
        int cnt=0;
        while(n%p==0){
            n/=p;
            cnt++;
        }
        res.push_back({p,cnt});
    }
    if(n>1) res.push_back({n,1});
    return res;
}

vector<ll> divisors(ll n){
    vector<ll> res;
    for(ll i=1;i*i<=n;i++){
        if(n%i) continue;
        res.push_back(i);
        if(i*i!=n) res.push_back(n/i);
    }
    sort(all(res));
    return res;
}

bool is_prime(ll n){
    if(n<2) return false;
    if(n%2==0) return n==2;
    for(ll i=3;i*i<=n;i+=2){
        if(n%i==0) return false;
    }
    return true;
}

template<class T>
struct FenwickTree{
    int n;
    vector<T> data;

    FenwickTree(int n=0):n(n),data(n+1,T()){}

    void add(int p,T x){
        assert(0<=p&&p<n);
        for(++p;p<=n;p+=p&-p) data[p]+=x;
    }

    T sum(int r) const{
        assert(0<=r&&r<=n);
        T res=T();
        for(;r>0;r-=r&-r) res+=data[r];
        return res;
    }

    T sum(int l,int r) const{
        return sum(r)-sum(l);
    }
};

template<class S,S(*op)(S,S),S(*e)()>
struct SegTree{
    int _n,size,log;
    vector<S> d;

    SegTree(int n=0){
        init(n);
    }

    SegTree(const vector<S>& v){
        init((int)v.size());
        for(int i=0;i<(int)v.size();i++) d[size+i]=v[i];
        for(int i=size-1;i>=1;i--) update(i);
    }

    void init(int n){
        _n=n;
        size=1;
        log=0;
        while(size<n){
            size<<=1;
            log++;
        }
        d.assign(2*size,e());
    }

    void update(int k){
        d[k]=op(d[2*k],d[2*k+1]);
    }

    void set(int p,S x){
        assert(0<=p&&p<_n);
        d[p+size]=x;
        for(int i=1;i<=log;i++) update((p+size)>>i);
    }

    S get(int p) const{
        assert(0<=p&&p<_n);
        return d[p+size];
    }

    S prod(int l,int r) const{
        assert(0<=l&&l<=r&&r<=_n);
        S sml=e(),smr=e();
        l+=size;
        r+=size;
        while(l<r){
            if(l&1) sml=op(sml,d[l++]);
            if(r&1) smr=op(d[--r],smr);
            l>>=1;
            r>>=1;
        }
        return op(sml,smr);
    }

    S all_prod() const{
        return d[1];
    }

    template<class F>
    int max_right(int l,F f) const{
        assert(0<=l&&l<=_n);
        assert(f(e()));
        if(l==_n) return _n;
        l+=size;
        S sm=e();
        do{
            while(!(l&1)) l>>=1;
            if(!f(op(sm,d[l]))){
                while(l<size){
                    l*=2;
                    if(f(op(sm,d[l]))){
                        sm=op(sm,d[l]);
                        l++;
                    }
                }
                return l-size;
            }
            sm=op(sm,d[l]);
            l++;
        }while((l&-l)!=l);
        return _n;
    }

    template<class F>
    int min_left(int r,F f) const{
        assert(0<=r&&r<=_n);
        assert(f(e()));
        if(r==0) return 0;
        r+=size;
        S sm=e();
        do{
            --r;
            while(r>1&&(r&1)) r>>=1;
            if(!f(op(d[r],sm))){
                while(r<size){
                    r=r*2+1;
                    if(f(op(d[r],sm))){
                        sm=op(d[r],sm);
                        r--;
                    }
                }
                return r+1-size;
            }
            sm=op(d[r],sm);
        }while((r&-r)!=r);
        return 0;
    }
};

struct DSU{
    vector<int> parent_or_size;

    DSU(int n=0):parent_or_size(n,-1){}

    int merge(int a,int b){
        assert(0<=a&&a<(int)parent_or_size.size());
        assert(0<=b&&b<(int)parent_or_size.size());
        a=leader(a);
        b=leader(b);
        if(a==b) return a;
        if(-parent_or_size[a] < -parent_or_size[b]) swap(a,b);
        parent_or_size[a]+=parent_or_size[b];
        parent_or_size[b]=a;
        return a;
    }

    bool same(int a,int b){
        return leader(a)==leader(b);
    }

    int leader(int a){
        assert(0<=a&&a<(int)parent_or_size.size());
        if(parent_or_size[a]<0) return a;
        return parent_or_size[a]=leader(parent_or_size[a]);
    }

    int size(int a){
        return -parent_or_size[leader(a)];
    }

    vector<vector<int>> groups(){
        int n=parent_or_size.size();
        vector<int> leader_buf(n),group_size(n);
        rep(i,n){
            leader_buf[i]=leader(i);
            group_size[leader_buf[i]]++;
        }
        vector<vector<int>> result(n);
        rep(i,n) result[leader_buf[i]].push_back(i);
        result.erase(
            remove_if(all(result),[](const vector<int>& v){return v.empty();}),
            result.end()
        );
        return result;
    }
};

vector<int> bfs(const Graph& g,int s){
    vector<int> dist(g.size(),-1);
    queue<int> q;
    dist[s]=0;
    q.push(s);
    while(!q.empty()){
        int v=q.front();
        q.pop();
        for(int to:g[v]){
            if(dist[to]!=-1) continue;
            dist[to]=dist[v]+1;
            q.push(to);
        }
    }
    return dist;
}

vector<ll> dijkstra(const vector<vector<pair<int,ll>>>& g,int s){
    vector<ll> dist(g.size(),LINF);
    priority_queue<pair<ll,int>,vector<pair<ll,int>>,greater<pair<ll,int>>> pq;
    dist[s]=0;
    pq.push({0,s});
    while(!pq.empty()){
        pair<ll,int> current=pq.top();
        pq.pop();
        ll d=current.first;
        int v=current.second;
        if(d!=dist[v]) continue;
        for(const pair<int,ll>& edge:g[v]){
            int to=edge.first;
            ll c=edge.second;
            if(chmin(dist[to],d+c)){
                pq.push({dist[to],to});
            }
        }
    }
    return dist;
}

vector<int> bfs01(const vector<vector<pair<int,int>>>& g,int s){
    vector<int> dist(g.size(),INF);
    deque<int> q;
    dist[s]=0;
    q.push_front(s);
    while(!q.empty()){
        int v=q.front();
        q.pop_front();
        for(const pair<int,int>& edge:g[v]){
            int to=edge.first;
            int c=edge.second;
            if(dist[to]<=dist[v]+c) continue;
            dist[to]=dist[v]+c;
            if(c==0) q.push_front(to);
            else q.push_back(to);
        }
    }
    return dist;
}

vector<int> topological_sort(const Graph& g){
    int n=g.size();
    vector<int> indeg(n);
    for(auto& v:g) for(int to:v) indeg[to]++;
    queue<int> q;
    rep(i,n) if(indeg[i]==0) q.push(i);
    vector<int> res;
    while(!q.empty()){
        int v=q.front();
        q.pop();
        res.push_back(v);
        for(int to:g[v]){
            if(--indeg[to]==0) q.push(to);
        }
    }
    return res;
}

template<class T>
struct PrefixSum2D{
    int h,w;
    vector<vector<T>> s;

    PrefixSum2D(const vector<vector<T>>& a){
        h=a.size();
        w=a[0].size();
        s.assign(h+1,vector<T>(w+1));
        rep(i,h) rep(j,w)
            s[i+1][j+1]=a[i][j]+s[i][j+1]+s[i+1][j]-s[i][j];
    }

    T query(int x1,int y1,int x2,int y2) const{
        return s[x2][y2]-s[x1][y2]-s[x2][y1]+s[x1][y1];
    }
};

template<class T>
struct LazySegTree{
    int n,size,log;
    vector<T> data,lazy;
    function<T(T,T)> op;
    function<T(T,int)> mapping;
    function<T(T,T)> composition;
    T e,id;

    LazySegTree(
        int n,
        T e,
        T id,
        function<T(T,T)> op,
        function<T(T,int)> mapping,
        function<T(T,T)> composition
    ):e(e),id(id),op(op),mapping(mapping),composition(composition){
        size=1;
        log=0;
        while(size<n){
            size<<=1;
            log++;
        }
        data.assign(2*size,e);
        lazy.assign(size,id);
        this->n=n;
    }

    void update(int k){
        data[k]=op(data[2*k],data[2*k+1]);
    }

    void all_apply(int k,T f){
        data[k]=mapping(f,data[k]);
        if(k<size) lazy[k]=composition(f,lazy[k]);
    }

    void push(int k){
        if(lazy[k]!=id){
            all_apply(2*k,lazy[k]);
            all_apply(2*k+1,lazy[k]);
            lazy[k]=id;
        }
    }

    void set(int p,T x){
        p+=size;
        for(int i=log;i>=1;i--) push(p>>i);
        data[p]=x;
        for(int i=1;i<=log;i++) update(p>>i);
    }

    T get(int p){
        p+=size;
        for(int i=log;i>=1;i--) push(p>>i);
        return data[p];
    }

    T prod(int l,int r){
        if(l==r) return e;
        l+=size;
        r+=size;
        for(int i=log;i>=1;i--){
            if(((l>>i)<<i)!=l) push(l>>i);
            if(((r>>i)<<i)!=r) push((r-1)>>i);
        }
        T sml=e,smr=e;
        while(l<r){
            if(l&1) sml=op(sml,data[l++]);
            if(r&1) smr=op(data[--r],smr);
            l>>=1;
            r>>=1;
        }
        return op(sml,smr);
    }

    T all_prod(){
        return data[1];
    }

    void apply(int p,T f){
        p+=size;
        for(int i=log;i>=1;i--) push(p>>i);
        data[p]=mapping(f,data[p]);
        for(int i=1;i<=log;i++) update(p>>i);
    }

    void apply(int l,int r,T f){
        if(l==r) return;
        l+=size;
        r+=size;
        for(int i=log;i>=1;i--){
            if(((l>>i)<<i)!=l) push(l>>i);
            if(((r>>i)<<i)!=r) push((r-1)>>i);
        }
        int l2=l,r2=r;
        while(l<r){
            if(l&1) all_apply(l++,f);
            if(r&1) all_apply(--r,f);
            l>>=1;
            r>>=1;
        }
        l=l2;
        r=r2;
        for(int i=1;i<=log;i++){
            if(((l>>i)<<i)!=l) update(l>>i);
            if(((r>>i)<<i)!=r) update((r-1)>>i);
        }
    }
};

template<int mod>
struct ModInt{
    int v;

    ModInt(long long x=0){
        x%=mod;
        if(x<0) x+=mod;
        v=x;
    }

    ModInt& operator+=(const ModInt& x){
        v+=x.v;
        if(v>=mod) v-=mod;
        return *this;
    }

    ModInt& operator-=(const ModInt& x){
        v-=x.v;
        if(v<0) v+=mod;
        return *this;
    }

    ModInt& operator*=(const ModInt& x){
        v=(long long)v*x.v%mod;
        return *this;
    }

    ModInt& operator/=(const ModInt& x){
        return *this*=x.pow(mod-2);
    }

    ModInt operator+(const ModInt& x)const{
        return ModInt(*this)+=x;
    }

    ModInt operator-(const ModInt& x)const{
        return ModInt(*this)-=x;
    }

    ModInt operator*(const ModInt& x)const{
        return ModInt(*this)*=x;
    }

    ModInt operator/(const ModInt& x)const{
        return ModInt(*this)/=x;
    }

    ModInt operator-()const{
        return ModInt(-v);
    }

    bool operator==(const ModInt& x)const{
        return v==x.v;
    }

    bool operator!=(const ModInt& x)const{
        return v!=x.v;
    }

    ModInt pow(long long n)const{
        ModInt a=*this,r=1;
        while(n){
            if(n&1) r*=a;
            a*=a;
            n>>=1;
        }
        return r;
    }
};

using mint = ModInt<MOD>;
using mint1 = ModInt<MOD1>;

template<class Mint>
struct Comb{
    vector<Mint> fact,ifact;

    Comb(int n=0){
        init(n);
    }

    void init(int n){
        fact.resize(n+1);
        ifact.resize(n+1);
        fact[0]=1;
        for(int i=1;i<=n;i++) fact[i]=fact[i-1]*i;
        ifact[n]=Mint(1)/fact[n];
        //ifact[n]=fact[n].pow(MOD-2);
        for(int i=n;i>=1;i--) ifact[i-1]=ifact[i]*i;
    }

    Mint C(int n,int r) const{
        if(r<0||r>n) return 0;
        return fact[n]*ifact[r]*ifact[n-r];
    }

    Mint P(int n,int r) const{
        if(r<0||r>n) return 0;
        return fact[n]*ifact[n-r];
    }
};

vector<int> sieve(int n){
    vector<bool> prime(n+1,true);
    vector<int> res;
    if(n>=0) prime[0]=false;
    if(n>=1) prime[1]=false;
    for(int i=2;i<=n;i++){
        if(!prime[i]) continue;
        res.push_back(i);
        if((ll)i*i<=n){
            for(int j=i*i;j<=n;j+=i) prime[j]=false;
        }
    }
    return res;
}

struct LCA{
    int n,log;
    vector<vector<int>> up;
    vector<int> depth;

    LCA(const Graph& g,int root=0){
        n=g.size();
        log=1;
        while((1<<log)<=n) log++;
        up.assign(log,vector<int>(n));
        depth.assign(n,-1);

        queue<int> q;
        depth[root]=0;
        up[0][root]=root;
        q.push(root);

        while(!q.empty()){
            int v=q.front();
            q.pop();
            for(int to:g[v]){
                if(depth[to]!=-1) continue;
                depth[to]=depth[v]+1;
                up[0][to]=v;
                q.push(to);
            }
        }

        for(int k=1;k<log;k++){
            rep(v,n) up[k][v]=up[k-1][up[k-1][v]];
        }
    }

    int jump(int v,int k) const{
        rep(i,log){
            if(k>>i&1) v=up[i][v];
        }
        return v;
    }

    int lca(int a,int b) const{
        if(depth[a]<depth[b]) swap(a,b);
        a=jump(a,depth[a]-depth[b]);
        if(a==b) return a;
        for(int k=log-1;k>=0;k--){
            if(up[k][a]!=up[k][b]){
                a=up[k][a];
                b=up[k][b];
            }
        }
        return up[0][a];
    }

    int dist(int a,int b) const{
        int c=lca(a,b);
        return depth[a]+depth[b]-2*depth[c];
    }
};

struct SCC{
    int n;
    vector<vector<int>> g,rg;
    vector<int> used,order,comp;

    SCC(int n):n(n),g(n),rg(n),used(n),comp(n,-1){}

    void add_edge(int from,int to){
        g[from].push_back(to);
        rg[to].push_back(from);
    }

    void dfs1(int v){
        used[v]=1;
        for(int to:g[v]) if(!used[to]) dfs1(to);
        order.push_back(v);
    }

    void dfs2(int v,int c){
        comp[v]=c;
        for(int to:rg[v]) if(comp[to]==-1) dfs2(to,c);
    }

    int build(){
        fill(all(used),0);
        order.clear();

        rep(v,n) if(!used[v]) dfs1(v);

        reverse(all(order));
        int cnt=0;

        for(int v:order){
            if(comp[v]!=-1) continue;
            dfs2(v,cnt++);
        }

        return cnt;
    }
};

struct TwoSAT{
    int n;
    SCC scc;

    TwoSAT(int n):n(n),scc(2*n){}

    int id(int x,bool value){
        return 2*x+(value?0:1);
    }

    void add_clause(int x,bool xv,int y,bool yv){
        scc.add_edge(id(x,!xv),id(y,yv));
        scc.add_edge(id(y,!yv),id(x,xv));
    }

    pair<bool,vector<bool>> solve(){
        int cnt=scc.build();
        vector<bool> ans(n);

        rep(i,n){
            if(scc.comp[2*i]==scc.comp[2*i+1]){
                return {false,{}};
            }
            ans[i]=scc.comp[2*i]>scc.comp[2*i+1];
        }

        return {true,ans};
    }
};

/*
template<class T>
struct Matrix{
    int h,w;
    vector<vector<T>> a;

    Matrix(int h,int w,T x=T()):h(h),w(w),a(h,vector<T>(w,x)){}

    static Matrix identity(int n){
        Matrix res(n,n);
        rep(i,n) res.a[i][i]=1;
        return res;
    }

    Matrix operator*(const Matrix& b) const{
        Matrix res(h,b.w);
        rep(i,h) rep(k,w){
            if(a[i][k]==T()) continue;
            rep(j,b.w){
                res.a[i][j]+=a[i][k]*b.a[k][j];
            }
        }
        return res;
    }

    Matrix pow(long long n) const{
        Matrix a=*this;
        Matrix r=identity(h);
        while(n){
            if(n&1) r=r*a;
            a=a*a;
            n>>=1;
        }
        return r;
    }
};
*/

//https://ei1333.github.io/luzhiled/snippets/graph/hungarian.html
template<class T> using Matrix = v<v<T>>;
template< typename T >
T hungarian(Matrix< T > &A) {
  const T infty = numeric_limits< T >::max();
  const int N = (int) A.size();
  const int M = (int) A[0].size();
  vector< int > P(M), way(M);
  vector< T > U(N, 0), V(M, 0), minV;
  vector< bool > used;

  for(int i = 1; i < N; i++) {
    P[0] = i;
    minV.assign(M, infty);
    used.assign(M, false);
    int j0 = 0;
    while(P[j0] != 0) {
      int i0 = P[j0], j1 = 0;
      used[j0] = true;
      T delta = infty;
      for(int j = 1; j < M; j++) {
        if(used[j]) continue;
        T curr = A[i0][j] - U[i0] - V[j];
        if(curr < minV[j]) minV[j] = curr, way[j] = j0;
        if(minV[j] < delta) delta = minV[j], j1 = j;
      }
      for(int j = 0; j < M; j++) {
        if(used[j]) U[P[j]] += delta, V[j] -= delta;
        else minV[j] -= delta;
      }
      j0 = j1;
    }
    do {
      P[j0] = P[way[j0]];
      j0 = way[j0];
    } while(j0 != 0);
  }
  return -V[0];
}

int main(){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    
}
