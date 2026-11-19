import sys, os, shutil, subprocess, tempfile, time, json

M32 = 0xFFFFFFFF
D4 = ((-1, 0), (1, 0), (0, -1), (0, 1))
LD = ((1, 0), (0, 1), (1, 1), (1, -1))

CPP = r"""#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <cmath>
#include <vector>
#include <algorithm>
#include <unordered_set>
using namespace std;
typedef uint32_t u32;
struct S{uint8_t b[81];uint8_t nx[3];u32 rng;int score;int parent;};
static bool HARD=false;
static uint8_t TAB[10];
static int W_SC=100,W_E=10,W_P=3;
static const int LD[4][2]={{1,0},{0,1},{1,1},{1,-1}};
static const int D4[4][2]={{-1,0},{1,0},{0,-1},{0,1}};
static inline int rnd(u32&rng,int n){
  rng=rng+0x6D2B79F5u;
  u32 t=(rng^(rng>>15))*(1u|rng);
  t=(t+((t^(t>>7))*(61u|t)))^t;
  double r=(double)(t^(t>>14))/4294967296.0;
  return (int)floor(r*n);
}
static int lineAt(const uint8_t*b,int i,int*out){
  int color=b[i];
  if(!color) return 0;
  int r0=i/9,c0=i%9,n=0;
  for(int d=0;d<4;d++){
    int run[16],rl=0;
    for(int s=-1;s<=1;s+=2){
      int r=r0+LD[d][0]*s,c=c0+LD[d][1]*s;
      while(r>=0&&r<9&&c>=0&&c<9&&b[r*9+c]==color){run[rl++]=r*9+c;r+=LD[d][0]*s;c+=LD[d][1]*s;}
    }
    if(rl>=4){for(int k=0;k<rl;k++)out[n++]=run[k];}
  }
  if(!n) return 0;
  out[n++]=i;
  return n;
}
static void randomColors(u32&rng,int n,uint8_t*o){
  int k=0;
  for(;k<n;k++) o[k]=rnd(rng,7)+1;
  for(;k<3;k++) o[k]=0;
}
static void commit(S&s,const uint8_t*colors,bool tagged,int src,int dst){
  int placed[3],np=0,n=0;
  if(HARD&&tagged&&TAB[rnd(s.rng,10)]==1){
    s.b[src]=colors[0];placed[np++]=src;
    n=1;
    int fr[4],nf=0,dr=dst/9,dc=dst%9;
    for(int d=0;d<4;d++){
      int r=dr+D4[d][0],c=dc+D4[d][1];
      if(r>=0&&r<9&&c>=0&&c<9&&!s.b[r*9+c]) fr[nf++]=r*9+c;
    }
    if(nf){
      int p=fr[rnd(s.rng,nf)];
      s.b[p]=colors[1];placed[np++]=p;
      n=2;
    }
  }
  for(;n<3;n++){
    if(!colors[n]) continue;
    int empty[81],ne=0;
    for(int i=0;i<81;i++) if(!s.b[i]) empty[ne++]=i;
    if(!ne) break;
    int p=empty[rnd(s.rng,ne)];
    s.b[p]=colors[n];placed[np++]=p;
  }
  for(int k=0;k<np;k++){
    if(s.b[placed[k]]){
      int cells[81];
      int c=lineAt(s.b,placed[k],cells);
      for(int j=0;j<c;j++) s.b[cells[j]]=0;
    }
  }
}
static int countEmpty(const S&s){
  int e=0;
  for(int i=0;i<81;i++) if(!s.b[i]) e++;
  return e;
}
static void applyMove(S&s,int from,int to){
  uint8_t colors[3]={s.nx[0],s.nx[1],s.nx[2]};
  int color=s.b[from];
  s.b[from]=0;s.b[to]=color;
  int cells[81];
  int n=lineAt(s.b,to,cells);
  if(n==0){
    uint8_t fresh[3];
    randomColors(s.rng,3,fresh);
    memcpy(s.nx,fresh,3);
    commit(s,colors,true,from,to);
  }else{
    for(int j=0;j<n;j++) s.b[cells[j]]=0;
    s.score+=(5*(n-4)*(n-3))/2+5;
  }
}
static long evalState(const S&s){
  int e=countEmpty(s);
  long pot=0;
  for(int i=0;i<81;i++){
    int c=s.b[i];
    if(!c) continue;
    int r=i/9,cc=i%9;
    for(int d=0;d<4;d++){
      int pr=r-LD[d][0],pc=cc-LD[d][1];
      if(pr>=0&&pr<9&&pc>=0&&pc<9&&s.b[pr*9+pc]==c) continue;
      int L=0,x=r,y=cc;
      while(x>=0&&x<9&&y>=0&&y<9&&s.b[x*9+y]==c){L++;x+=LD[d][0];y+=LD[d][1];}
      if(L>=2) pot+=(L-1)*(L-1);
    }
  }
  return (long)s.score*W_SC+(long)e*W_E+pot*W_P;
}
struct Mv{int from,to;};
static void genMoves(const S&s,vector<Mv>&out){
  out.clear();
  int comp[81];
  memset(comp,-1,sizeof comp);
  vector<vector<int>> cells;
  int st[81];
  for(int i=0;i<81;i++) if(!s.b[i]&&comp[i]<0){
    int id=cells.size();
    cells.push_back(vector<int>());
    int sp=0;
    st[sp++]=i;comp[i]=id;
    while(sp){
      int x=st[--sp];
      cells[id].push_back(x);
      int r=x/9,c=x%9;
      for(int d=0;d<4;d++){
        int rr=r+D4[d][0],cc=c+D4[d][1];
        if(rr<0||rr>8||cc<0||cc>8) continue;
        int y=rr*9+cc;
        if(!s.b[y]&&comp[y]<0){comp[y]=id;st[sp++]=y;}
      }
    }
  }
  for(int i=0;i<81;i++) if(s.b[i]){
    int r=i/9,c=i%9,seen[4],ns=0;
    for(int d=0;d<4;d++){
      int rr=r+D4[d][0],cc=c+D4[d][1];
      if(rr<0||rr>8||cc<0||cc>8) continue;
      int y=rr*9+cc;
      if(s.b[y]) continue;
      int id=comp[y];
      bool dup=false;
      for(int k=0;k<ns;k++) if(seen[k]==id) dup=true;
      if(dup) continue;
      seen[ns++]=id;
      for(size_t k=0;k<cells[id].size();k++) out.push_back({i,cells[id][k]});
    }
  }
}
static uint64_t hashS(const S&s){
  uint64_t h=1469598103934665603ULL;
  for(int i=0;i<81;i++){h^=s.b[i];h*=1099511628211ULL;}
  for(int i=0;i<3;i++){h^=s.nx[i];h*=1099511628211ULL;}
  h^=s.rng;h*=1099511628211ULL;
  h^=(uint64_t)s.score;h*=1099511628211ULL;
  return h;
}
struct Cand{long ev;int pi;uint8_t f,t;};
static bool cmpCand(const Cand&a,const Cand&b){return a.ev>b.ev;}
int main(int argc,char**argv){
  if(argc<5) return 2;
  u32 seed=(u32)strtoul(argv[1],0,10);
  int W=atoi(argv[2]);
  int target=atoi(argv[3]);
  HARD=atoi(argv[4])==2;
  S s0;
  memset(&s0,0,sizeof s0);
  s0.rng=seed;
  for(int i=0;i<3;i++) TAB[rnd(s0.rng,10)]=1;
  uint8_t cl[3];
  randomColors(s0.rng,3,cl);commit(s0,cl,false,0,0);
  randomColors(s0.rng,2,cl);commit(s0,cl,false,0,0);
  randomColors(s0.rng,3,s0.nx);
  vector<int> hpar,hmv;
  hpar.push_back(-1);hmv.push_back(0);
  s0.parent=0;
  vector<S> beam(1,s0);
  int bestScore=0,step=0,goal=-1;
  vector<Mv> mvs;
  while(!beam.empty()&&goal<0){
    vector<Cand> cands;
    for(int pi=0;pi<(int)beam.size()&&goal<0;pi++){
      genMoves(beam[pi],mvs);
      for(size_t k=0;k<mvs.size();k++){
        S c=beam[pi];
        applyMove(c,mvs[k].from,mvs[k].to);
        if(c.score>=target){
          hpar.push_back(beam[pi].parent);
          hmv.push_back(mvs[k].from*81+mvs[k].to);
          goal=(int)hpar.size()-1;
          break;
        }
        if(countEmpty(c)==0) continue;
        Cand cd;cd.ev=evalState(c);cd.pi=pi;cd.f=mvs[k].from;cd.t=mvs[k].to;
        cands.push_back(cd);
      }
    }
    if(goal>=0) break;
    step++;
    size_t keep=(size_t)W*3;
    if(cands.size()>keep){
      nth_element(cands.begin(),cands.begin()+keep,cands.end(),cmpCand);
      cands.resize(keep);
    }
    sort(cands.begin(),cands.end(),cmpCand);
    vector<S> nb;
    unordered_set<uint64_t> seen;
    for(size_t k=0;k<cands.size()&&(int)nb.size()<W;k++){
      S x=beam[cands[k].pi];
      applyMove(x,cands[k].f,cands[k].t);
      if(!seen.insert(hashS(x)).second) continue;
      hpar.push_back(beam[cands[k].pi].parent);
      hmv.push_back(cands[k].f*81+cands[k].t);
      x.parent=(int)hpar.size()-1;
      nb.push_back(x);
      if(x.score>bestScore) bestScore=x.score;
    }
    beam.swap(nb);
    if(step%50==0) fprintf(stderr,"step %d best %d\n",step,bestScore);
  }
  if(goal<0){fprintf(stderr,"fail best %d steps %d\n",bestScore,step);return 1;}
  vector<int> path;
  for(int g=goal;g>0;g=hpar[g]) path.push_back(hmv[g]);
  reverse(path.begin(),path.end());
  for(size_t k=0;k<path.size();k++) printf("%d %d\n",path[k]/81,path[k]%81);
  return 0;
}
"""


def inb(r, c):
    return 0 <= r < 9 and 0 <= c < 9


class Game:
    def __init__(self, seed, hard):
        self.rng = seed & M32
        self.hard = hard
        self.b = [0] * 81
        self.score = 0
        self.tab = [0] * 10
        for _ in range(3):
            self.tab[self.rnd(10)] = 1
        self.commit(self.colors(3), False, 0, 0)
        self.commit(self.colors(2), False, 0, 0)
        self.nx = self.colors(3)

    def rand(self):
        self.rng = (self.rng + 0x6D2B79F5) & M32
        t = ((self.rng ^ (self.rng >> 15)) * (1 | self.rng)) & M32
        t = ((t + (((t ^ (t >> 7)) * (61 | t)) & M32)) & M32) ^ t
        return (t ^ (t >> 14)) / 4294967296.0

    def rnd(self, n):
        return int(self.rand() * n)

    def colors(self, n):
        out = [self.rnd(7) + 1 for _ in range(n)]
        return out + [0] * (3 - n)

    def nbr(self, i):
        r, c = divmod(i, 9)
        return [(r + a) * 9 + c + d for a, d in D4 if inb(r + a, c + d)]

    def line_at(self, i):
        color = self.b[i]
        if not color:
            return None
        r0, c0 = divmod(i, 9)
        cells = []
        for dr, dc in LD:
            run = []
            for s in (1, -1):
                r, c = r0 + dr * s, c0 + dc * s
                while inb(r, c) and self.b[r * 9 + c] == color:
                    run.append(r * 9 + c)
                    r += dr * s
                    c += dc * s
            if len(run) >= 4:
                cells += run
        if not cells:
            return None
        cells.append(i)
        return cells

    def commit(self, colors, tagged, src, dst):
        placed = []
        n = 0
        if self.hard and tagged and self.tab[self.rnd(10)] == 1:
            self.b[src] = colors[0]
            placed.append(src)
            n = 1
            free = [x for x in self.nbr(dst) if not self.b[x]]
            if free:
                p = free[self.rnd(len(free))]
                self.b[p] = colors[1]
                placed.append(p)
                n = 2
        while n < 3:
            if colors[n]:
                empty = [i for i in range(81) if not self.b[i]]
                if not empty:
                    break
                p = empty[self.rnd(len(empty))]
                self.b[p] = colors[n]
                placed.append(p)
            n += 1
        for p in placed:
            if self.b[p]:
                cells = self.line_at(p)
                if cells:
                    for c in cells:
                        self.b[c] = 0

    def path_len(self, frm, to):
        if not self.b[frm] or self.b[to]:
            return None
        dist = {to: 0}
        q = [to]
        for x in q:
            for n in self.nbr(x):
                if not self.b[n] and n not in dist:
                    dist[n] = dist[x] + 1
                    q.append(n)
        ds = [dist[n] for n in self.nbr(frm) if n in dist]
        return min(ds) + 1 if ds else None

    def play(self, frm, to):
        colors = self.nx[:]
        color = self.b[frm]
        self.b[frm] = 0
        self.b[to] = color
        hit = self.line_at(to) is not None
        self.b[to] = 0
        self.b[frm] = color
        if not hit:
            self.nx = self.colors(3)
        self.b[frm] = 0
        self.b[to] = color
        cells = self.line_at(to)
        if cells:
            for c in cells:
                self.b[c] = 0
            n = len(cells)
            self.score += 5 * (n - 4) * (n - 3) // 2 + 5
            return True
        self.commit(colors, True, frm, to)
        return any(v == 0 for v in self.b)


def verify(seed, hard, moves, target):
    g = Game(seed, hard)
    lens = []
    for k, (f, t) in enumerate(moves):
        ln = g.path_len(f, t)
        if ln is None:
            return False, g.score, lens
        lens.append(ln)
        if not g.play(f, t):
            return False, g.score, lens
    return g.score >= target, g.score, lens


def find_compiler():
    for name in ("g++", "c++", "clang++"):
        p = shutil.which(name)
        if p:
            return p
    return None


def build(compiler, workdir):
    exe = os.path.join(workdir, "solver.exe" if os.name == "nt" else "solver")
    src = os.path.join(workdir, "solver.cpp")
    with open(src, "w") as f:
        f.write(CPP)
    r = subprocess.run([compiler, "-O2", "-o", exe, src], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("compile failed:\n" + r.stderr[-800:])
    return exe


def run(exe, seed, width, target, level):
    r = subprocess.run([exe, str(seed), str(width), str(target), str(level)], capture_output=True, text=True)
    if r.returncode != 0:
        return None
    return [tuple(int(x) for x in ln.split()) for ln in r.stdout.splitlines() if ln.strip()]


JS = r"""(async()=>{
const SEED=%(seed)d,HARD=%(hard)s,M=%(moves)s;
const $=id=>document.getElementById(id);
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
const settle=async()=>{let idle=0;while(idle<8){await sleep(100);const m=$('mask');if(m.classList.contains('on')){idle=0;const i=m.querySelector('input');if(i)i.value=String(SEED);m.querySelector('button').click();}else idle++;}};
$('btnSeed').click();await settle();
if(($('chk').getAttribute('aria-checked')==='true')!==HARD){$('chk').click();await settle();}
await sleep(1000);
const cv=$('board');
function tap(i){
  const rc=cv.getBoundingClientRect(),r=Math.floor(i/9),c=i%%9;
  const x=rc.left+(c+0.5)*rc.width/9,y=rc.top+(r+0.5)*rc.height/9;
  cv.dispatchEvent(new PointerEvent('pointerdown',{clientX:x,clientY:y,bubbles:true,cancelable:true}));
}
for(let k=0;k<M.length;k++){
  const [f,t,len]=M[k];
  tap(f);await sleep(40);
  tap(t);
  await sleep(%(base)d+%(per)d*len);
  if(k%%50===0)console.log(k+1,$('score').textContent);
}
console.log('done',$('score').textContent);
})();
"""


def main():
    a = sys.argv[1:]
    seed = int(a[0]) if len(a) > 0 else int(input("seed: "))
    target = int(a[1]) if len(a) > 1 else int(input("target: "))
    mode = a[2] if len(a) > 2 else input("mode (n/h): ")
    hard = mode.strip().lower().startswith("h")
    level = 2 if hard else 1
    if not 0 <= seed <= 4294967295:
        sys.exit("seed out of range")

    compiler = find_compiler()
    if not compiler:
        sys.exit("no C++ compiler found (g++/clang++)")
    exe = build(compiler, tempfile.mkdtemp(prefix="colorline_"))

    t0 = time.time()
    for w in (20, 50, 100, 200, 400, 800):
        print("width", w, flush=True)
        moves = run(exe, seed, w, target, level)
        if not moves:
            continue
        ok, score, lens = verify(seed, hard, moves, target)
        if not ok:
            continue
        name = "colorline_%s_seed%d_target%d.js" % ("hard" if hard else "normal", seed, target)
        data = JS % dict(seed=seed, hard="true" if hard else "false",
                         moves=json.dumps([[f, t, l] for (f, t), l in zip(moves, lens)], separators=(",", ":")),
                         base=600, per=55)
        with open(name, "w", encoding="utf-8") as f:
            f.write(data)
        print("ok moves=%d score=%d time=%.1fs file=%s" % (len(moves), score, time.time() - t0, name))
        return
    print("failed")


if __name__ == "__main__":
    main()
