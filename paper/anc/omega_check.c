// Sanity check of the (proved) majorant  Omega^-(e) <= m(e/Q),
//   Omega(e) = sum_{r sqfree,(r,e)=1} mu(r) w(er/Q)/phi(r),   m(u) = ( sum_{mu(r)=-1} w(ur)/phi(r) - w(u) )^+ .
// Reports: violations (should be 0), negative mass by band of e/(eta Q), majorant mass, max Omega/(Q/e)^2 etc.
// usage: omega_check Q kind(0 sharp,1 lsmooth) eta
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
static long gcdl(long a, long b){ while(b){ long t=a%b; a=b; b=t;} return a; }
int main(int argc, char**argv){
  long Q=atol(argv[1]); int kind=atoi(argv[2]); double eta=atof(argv[3]); double L=log(1.0/eta);
  int *mu=malloc((Q+1)*sizeof(int)); double *phi=malloc((Q+1)*sizeof(double)); char *comp=calloc(Q+1,1);
  for(long i=0;i<=Q;i++){ mu[i]=1; phi[i]=(double)i; }
  for(long p=2;p<=Q;p++) if(!comp[p]){ for(long m=p;m<=Q;m+=p){ if(m>p) comp[m]=1; mu[m]=-mu[m]; phi[m]*=(1.0-1.0/p);} if(p<=Q/p) for(long m=p*p;m<=Q;m+=p*p) mu[m]=0; }
  double *w=malloc((Q+1)*sizeof(double));
  for(long q=0;q<=Q;q++){ double u=(double)q/Q, v=0; if(q>0 && u>=eta*(1-1e-15)){ double y=-log(u); v = (kind==0)? 1.0/(u*u) : pow(sin(M_PI*y/L),2)/(u*u);} w[q]=v; }
  double *Om=calloc(Q+1,sizeof(double)), *Mj=calloc(Q+1,sizeof(double));
  for(long r=1;r<=Q;r++){ if(!mu[r]) continue; double cr=mu[r]/phi[r];
    for(long e=1;e*r<=Q;e++){ double wv=w[e*r]; if(wv==0) continue;
      if(mu[r]==-1) Mj[e]+= wv/phi[r];
      if(r>1 && gcdl(e,r)!=1) continue; Om[e]+=cr*wv; } }
  double W=0, neg=0, maj=0, worst=0; long viol=0, nneg=0; double bands[7]={0}; double bl[8]={0,0.5,1,1.5,2,2.5,3,1e18};
  double maxratio=0; long emaxratio=0; double emaxneg=0;
  for(long e=1;e<=Q;e++){
    double m = Mj[e]-w[e]; if(m<0) m=0;
    double on = Om[e]<0 ? -Om[e] : 0;
    W += Om[e]*phi[e]; neg += on*phi[e]; maj += m*phi[e];
    if(on > m*(1+1e-12)+1e-300){ viol++; double d=on-m; if(d>worst) worst=d; }
    if(on>0){ nneg++; if(e>emaxneg) emaxneg=e; double x=e/(eta*Q); for(int b=0;b<7;b++) if(x>=bl[b]&&x<bl[b+1]) bands[b]+=on*phi[e]; }
    if(on>0 && m>0){ double rr=on/m; if(rr>maxratio){maxratio=rr; emaxratio=e;} }
  }
  printf("Q=%ld kind=%s eta=%g: W(=H check)=%.6e  violations of Omega^- <= m(e/Q): %ld (worst excess %.3e)\n",Q,kind?"lsmooth":"sharp",eta,W,viol,worst);
  printf("  neg mass/W=%.5f   majorant mass sum m(e/Q)phi(e)/W=%.5f   largest e with Omega<0: e/(eta Q)=%.3f   max Omega^-/m=%.4f at e/(etaQ)=%.3f\n",
         neg/W, maj/W, emaxneg/(eta*Q), maxratio, emaxratio/(eta*Q));
  printf("  neg-mass fraction by band e/(eta Q): [0,.5) %.3f [.5,1) %.3f [1,1.5) %.3f [1.5,2) %.3f [2,2.5) %.3f [2.5,3) %.3f [3,inf) %.3f\n",
     bands[0]/neg,bands[1]/neg,bands[2]/neg,bands[3]/neg,bands[4]/neg,bands[5]/neg,bands[6]/neg);
  return 0;
}
