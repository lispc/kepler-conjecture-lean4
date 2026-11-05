import mpmath as mp
mp.mp.dps = 40
pi = mp.pi
def deltaX(x1,x2,x3,x4,x5,x6):
    return (x1*x4*(-x1+x2+x3-x4+x5+x6)
          + x2*x5*(x1-x2+x3+x4-x5+x6)
          + x3*x6*(x1+x2-x3+x4+x5-x6)
          - x2*x3*x4 - x1*x3*x5 - x1*x2*x6 - x4*x5*x6)
def deltaX4(x1,x2,x3,x4,x5,x6):
    return (-x2*x3 - x1*x4 + x2*x5 + x3*x6 - x5*x6 + x1*(-x1+x2+x3-x4+x5+x6))
def atn2(x,y):
    if abs(y) < x: return mp.atan(y/x)
    if y > 0: return pi/2 - mp.atan(x/y)
    if y < 0: return -pi/2 - mp.atan(x/y)
    return pi
def dihXf(x1,x2,x3,x4,x5,x6):
    return pi/2 + atn2(mp.sqrt(4*x1*deltaX(x1,x2,x3,x4,x5,x6)), -deltaX4(x1,x2,x3,x4,x5,x6))
def dihY(y1,y2,y3,y4,y5,y6):
    return dihXf(y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6)
def solY(y1,y2,y3,y4,y5,y6):
    return dihY(y1,y2,y3,y4,y5,y6)+dihY(y2,y3,y1,y5,y6,y4)+dihY(y3,y1,y2,y6,y4,y5)-pi
def volXf(x1,x2,x3,x4,x5,x6): return mp.sqrt(deltaX(x1,x2,x3,x4,x5,x6))/12
def volY(y1,y2,y3,y4,y5,y6): return volXf(y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6)
sol0 = 3*mp.acos(mp.mpf(1)/3) - pi
tau0 = 4*pi - 20*sol0
mm1 = sol0*mp.sqrt(8)/tau0
mm2 = (6*sol0-pi)*mp.sqrt(2)/(6*tau0)
h0 = mp.mpf('1.26')
def lmfun(h): return (h0-h)/(h0-1) if h <= h0 else mp.mpf(0)
def vol4f(y1,y2,y3,y4,y5,y6,f=lmfun):
    s = (solY(y1,y2,y3,y4,y5,y6)+solY(y1,y5,y6,y4,y2,y3)
        +solY(y4,y5,y3,y1,y2,y6)+solY(y4,y2,y6,y1,y5,y3))
    d = (f(y1/2)*dihY(y1,y2,y3,y4,y5,y6)+f(y2/2)*dihY(y2,y3,y1,y5,y6,y4)
        +f(y3/2)*dihY(y3,y1,y2,y6,y4,y5)+f(y4/2)*dihY(y4,y3,y5,y1,y6,y2)
        +f(y5/2)*dihY(y5,y1,y6,y2,y4,y3)+f(y6/2)*dihY(y6,y1,y5,y3,y4,y2))
    return (2*mm1/pi)*s - (8*mm2/pi)*d
def g4(v,f=lmfun): return volY(*v) - vol4f(*v,f)

base=(mp.mpf(2),)*6
print("g4(2,...)      =", mp.nstr(g4(base),12))
print("g4(2.001^6)    =", mp.nstr(g4((mp.mpf('2.001'),)*6),12))
print("\n== 逐变量单调性 (其余=2, 抬到 2.001) ==")
for k in range(6):
    v=list(base); v[k]=mp.mpf('2.001')
    print(f"  raise y{k+1}: g4 = {mp.nstr(g4(tuple(v)),10)}  (delta vs 0 = {mp.nstr(g4(tuple(v)),6)})")
print("\n== 混合 ==")
for t in ['2.0001','2.001']:
    for k in [1,2,3,6]:
        v=[mp.mpf(t)]*k + [mp.mpf(2)]*(6-k)
        print(f"  first {k} vars = {t}: g4 = {mp.nstr(g4(tuple(v)),10)}")

print("\n== 全域单调性抽样：对每个变量做 (2.0 -> 2.001) 的差，其余变量取盒内随机/端点 ==")
import itertools, random
random.seed(7)
pts=[]
for _ in range(6):
    pts.append(tuple(mp.mpf(random.choice(['2.0','2.0005','2.001'])) for _ in range(6)))
pts += [tuple(mp.mpf('2.001') if i%2==0 else mp.mpf('2.0') for i in range(6)),
        (mp.mpf('2.0'),)*5+(mp.mpf('2.001'),)]
bad=0
for idx,p in enumerate(pts):
    for k in range(6):
        lo=list(p); hi=list(p); hi[k]=mp.mpf('2.001'); lo[k]=mp.mpf('2.0')
        d = g4(tuple(hi))-g4(tuple(lo))
        if d < 0: bad+=1; print(f"  !! 非单调 point{idx} var{k+1}: diff={mp.nstr(d,8)}")
print("  单调性违反次数:", bad, "/", len(pts)*6)

print("\n== 第二条 IYOUOBFsharpv2 的角点 (√8,2,2,2,2,2) ==")
v=(mp.sqrt(8),)+(mp.mpf(2),)*5
print("  g4 =", mp.nstr(g4(v),12), "  lmfun(√8/2) =", mp.nstr(lmfun(mp.sqrt(8)/2),6))
v2=(mp.sqrt(8),mp.mpf('2.001'),mp.mpf('2.001'),mp.mpf(2),mp.mpf('2.001'),mp.mpf('2.001'))
print("  盒内同侧点 g4 =", mp.nstr(g4(v2),12))
