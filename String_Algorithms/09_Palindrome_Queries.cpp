#include<bits/stdc++.h>
#include<chrono>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>
using namespace std;
using namespace __gnu_pbds;

#define int long long int
#define REP(i,a,b) for (int i=a;i<b;i++)
#define Fill(a,n) REP(i,0,n){cin>>a[i];}
#define printVec(a,n) REP(i,0,n){cout<<a[i]<<' ';}cout<<endl;
#define debug(a) cout<<"debugging: "<<a<<endl;
#define pb push_back
#define fi first
#define se second
#define vi vector<int>
#define vpi vector<pair<int,int>>
#define FASTIO ios::sync_with_stdio(false);cin.tie(nullptr); cout.tie(nullptr);

const int inf = 1e16;
int mod=1e9+7;

void PrintBinary(int a){
    for(int i=62;i>=0;i--){
        if((a&(1ll<<i))) cout<<1;
        else cout<<0;
    }
    cout<<endl;
}

int binaryExpo(int a,int b,int mod){
   int ans=1;
   if (b==1)return a%mod;
   ans=binaryExpo(a,b/2,mod);
   ans=(ans*ans)%mod;
   if(b%2){
      ans=(ans*a)%mod;
   }
   return ans;
}
 
struct DSU{
    vector<int>parent;
    vector<int>size;

    DSU(int n):parent(n+1),size(n+1){};

    void Union(int a, int b){
        a = Find(a);
        b = Find(b);
        if(a==b)return;
        if (size[a] > size[b]) swap(a,b);
        parent[a] = b; 
        size[b] += size[a];
    }

    void Make(int a){
        parent[a] = a;
        size[a] = 1;
    }

    int Find(int a){
        int b = parent[a];
        if(a == b)return a;
        return parent[a] = Find(b);
    }
};

struct Segtree{

    int segarray;
    vector<int> segtree; //modify accordingly

    Segtree(int n, vector<int>& a): segarray(n), segtree(4*n){
        build(a);
    }

    void _build(vector<int>&a,int v,int left, int right){
        if(left == right){
            segtree[v]=a[left]; //modify acordingly
        }else{
            int middle = (left + right)/2;
            _build(a,2*v,left,middle);
            _build(a,2*v+1,middle+1,right);
            segtree[v] = (segtree[2*v] + segtree[2*v+1])%mod; // modify accordingly
        }
    }

    void build(vector<int>&a){
        _build(a,1,0,segarray-1);
    }

    // modify return type if needed
    int _query(int v,int left,int right, int qleft, int qright){
        if(qright<qleft){
            return {}; // identy value. modify accordingly
        }
        if(qleft == left && qright == right){
            return segtree[v];
        }
        int middle = (left + right)/2;
        return (_query(2*v,left,middle,qleft,min(qright,middle)) + _query(2*v+1,middle+1,right,max(qleft,middle+1),qright))%mod; //modify accordingly

        
        
    }

    int query(int left,int right){
        return _query(1,0,segarray-1,left,right);
    }

    void _update(int v,int left, int right, int pos, int newval){
        if(left == right){
            segtree[v]=(newval)%mod; //modify accordingly
            // segtree[v] = {newval};
        }else{
            int middle = (left + right)/2;
            if(pos<=middle){
                _update(2*v,left,middle,pos,newval);
            }else{
                _update(2*v+1,middle+1,right,pos,newval);
            }
            segtree[v] = (segtree[2*v] + segtree[2*v+1])%mod; //modify accordingly
            

        }
    }

    void update(int pos, int newval){
        _update(1,0,segarray-1,pos,newval);
    }

};

template <typename T>
using ordered_set = tree<T,null_type,less<T>,rb_tree_tag,tree_order_statistics_node_update> ;
// os.find_by_order(k);
// os.order_of_key(x);

struct Dinic {
    struct Edge {
        int to;
        int cap;
        int rev;
        bool real;
    };

    int n;
    vector<vector<Edge>> graph;
    vector<int> level, ptr;
    queue<int> q;

    Dinic(int n) : n(n), graph(n), level(n), ptr(n) {}

    void add_edge(int u, int v, int cap) {
        Edge a = {v, cap, (int)graph[v].size(),1};
        Edge b = {u, 0,   (int)graph[u].size(),0};
        graph[u].push_back(a);
        graph[v].push_back(b);
    }

    bool bfs(int s, int t) {
        fill(level.begin(), level.end(), -1);
        level[s] = 0;
        q = queue<int>();
        q.push(s);

        while (!q.empty()) {
            int u = q.front(); q.pop();
            for (auto &e : graph[u]) {
                if (level[e.to] < 0 && e.cap > 0) {
                    level[e.to] = level[u] + 1;
                    q.push(e.to);
                }
            }
        }
        return level[t] >= 0;
    }

    int dfs(int u, int t, int pushed) {
        if (pushed == 0) return 0;
        if (u == t) return pushed;

        for (int &cid = ptr[u]; cid < (int)graph[u].size(); cid++) {
            Edge &e = graph[u][cid];
            if (level[e.to] == level[u] + 1 && e.cap > 0) {
                int tr = dfs(e.to, t, min(pushed, e.cap));
                if (tr > 0) {
                    e.cap -= tr;
                    graph[e.to][e.rev].cap += tr;
                    return tr;
                }
            }
        }
        return 0;
    }

    int max_flow(int s, int t) {
        int flow = 0;
        while (bfs(s, t)) {
            fill(ptr.begin(), ptr.end(), 0);
            while (int pushed = dfs(s, t, LLONG_MAX)) {
                flow += pushed;
            }
        }
        return flow;
    }

    void dfs2(int v, vector<int>& vis){
        for(auto &e: graph[v]){
            if(!vis[e.to] && e.cap > 0){
                vis[e.to]=1;
                dfs2(e.to,vis);
            }
        }
    }
    set<pair<int,int>> remove_edges(int s){
        vector<int>vis(n,0);
        vis[s]=1;
        dfs2(s,vis);
        set<pair<int,int>> ans;
        for(int i =0;i<n;i++){
            if(!vis[i])continue;
            for(auto &e:graph[i]){
                if(!vis[e.to]){
                    if(e.to>i)ans.insert({i,e.to});
                    else ans.insert({e.to,i});
                }
            }
        }
        return ans;
    }
    
    void unit_decomposition(int s, int t, vector<vector<int>>& ans) {
        int n = graph.size();
        vector<int> ptr(n, 0);

        while (true) {
            vector<int> path;
            int v = s;
            path.push_back(v);

            while (v != t) {
                // advance pointer to next used edge
                // cout<<"came at v: "<<v+1<<endl;
                while (ptr[v] < graph[v].size() && (graph[v][ptr[v]].cap != 0 || !graph[v][ptr[v]].real))
                ptr[v]++;
                
                if (ptr[v] == graph[v].size())
                return;  // no more paths
                
                auto &e = graph[v][ptr[v]];
                e.cap = 1;          // restore capacity
                v = e.to;
                // cout<<"v "<<v+1<<endl;
                path.push_back(v);
            }

            ans.push_back(path);
        }
    } 
};

// binary exponentiation
int expo (int a, int b){
    if(b==0)return 1;
    int x = expo(a,b/2);
    x = (x*x)%mod;
    if(b&1) x = (x*a)%mod;
    return x;
}

void solve(){
    int n,m;cin>>n>>m;
    string s;cin>>s;
    vector<int> forward(n,0);
    vector<int> backward(n,0);
    int p = 1009;
    int p_rev = expo(p,mod-2);
    vector<int>p_pow(n,1);
    vector<int>p_revpow(n,1);
    for(int i = 1;i<n;i++){
        p_pow[i] = (p_pow[i-1] * p)%mod;
        p_revpow[i] = (p_revpow[i-1]*p_rev)%mod;
    }
    for(int i = 0;i<n;i++){
        forward[i] = ((s[i] - 'a') * p_pow[i])%mod;
        backward[i] = ((s[n-1-i] - 'a') * p_pow[i])%mod;
    }
    Segtree seg_forward(n,forward);
    Segtree seg_backward(n,backward);

    while(m--){
        int type;cin>>type;
        if(type==1){
            int index;cin>>index;
            char c;cin>>c;
            index--;
            int forward_value = ((c - 'a') * p_pow[index])%mod;
            int backward_value = ((c - 'a') * p_pow[n-1-index])%mod;
            seg_forward.update(index,forward_value);
            seg_backward.update(n-1-index,backward_value);
        }else if(type==2){
            int left,right;cin>>left>>right;
            left--;right--;
            int backleft = n-right-1;
            int backright = n - left - 1;

            int left_hash = (seg_forward.query(left,right) * p_revpow[left])%mod;
            int right_hash = (seg_backward.query(backleft,backright)*p_revpow[backleft])%mod;

            cout<<((left_hash == right_hash) ? "YES" : "NO" )<<endl;
        }
    }


}
int32_t main() {
    FASTIO
    solve();

    /*
        INTUTION:
        
        It is a heuristic solution not an exact solution. 
        a string is a palindrome if it is same from forward and backward, but to check that it would need 
        O(n) per query, to avoid that we compare hashes, of forward and backward substrings, if hashes dont match 
        they are definitly not equal, and if they do match, they can be equal, and maybe even not equal with 
        a small proabilty, we bet on this. 
    */
}