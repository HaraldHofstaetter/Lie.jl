#include<stdlib.h>
#include<stdint.h>
#include<stdio.h>
#include<assert.h>
#include<time.h>

#ifdef USE_INT128_T
typedef __int128_t INTEGER; 
#else
typedef __int64_t INTEGER;
#endif


static uint8_t **W;
static size_t *p1;
static size_t *p2;
static size_t *nn;
static size_t *ii;
static size_t *LWI;
static size_t *MDI;
static size_t n_lyndon;
static INTEGER *FACTORIAL;

static size_t lookup_size;
int *LUT;


void moebius_mu(size_t N, int mu[N]) {
    /* INPUT: N
     * OUTPUT: mu[n] = Moebius mu function of n+1, n=0,...,N-1
     * METHOD: see https://mathoverflow.net/questions/99473/calculating-m%C3%B6bius-function
     */
    for (int i=0; i<N; i++) {
        mu[i] = 0;
    }
    mu[0] = 1;
    for (int n=1; n<=N/2; n++) {
        int mu_n = mu[n-1];
        for(int i=2*n-1; i<N; i+=n) {
            mu[i] -= mu_n;
        }
    }
}

void number_of_lyndon_words(uint8_t K, size_t N, size_t nLW[N]) {
    /* INPUT: K ... number of letters
     *        N ... maximum lenght of lyndon words
     * OUTPUT: nLW[n] ... number of lyndon words with K letters of length n+1, n=0,...,N-1
     * METHOD: Witt's formula
     */
    unsigned int powK[N+1];
    powK[0] = 1;
    for (int i=1; i<=N; i++) {
        powK[i] = powK[i-1]*K;
    }
    
    int mu[N];
    moebius_mu(N, mu);

    for (int n=1; n<=N; n++) {
        int d = 1;
        int h = 0;
        while (d*d < n) {
            div_t d1r = div(n, d);
            if (d1r.rem==0) {
               int d1 = d1r.quot; 
               h += mu[d-1]*powK[d1]+mu[d1-1]*powK[d];
            }
            d++;
        }
        if (d*d == n) {
            h += mu[d-1]*powK[d];
        }
        nLW[n-1] = h/n;
    }
}

void print_word(size_t n, uint8_t w[]) {        
    for (int j=0; j<n; j++) {
           printf("%i", w[j]);
    }
}

size_t word_index(uint8_t K, uint8_t w[], size_t l, size_t r) {
    //size_t x = w[r];
    //size_t y = K;
    size_t x = 0;
    size_t y = 1;
    for (int j=r; j>= (signed) l; j--) { /* CAUTION! comparison between signed and unsigned */
        x += w[j]*y;
        y *= K;
    }
    return x + (y-1)/(K-1) - 1;
}

size_t find_lyndon_word_index(size_t l, size_t r, size_t wi) {
    while (l<=r) {
        size_t m = l + (r-l)/2;
        if (LWI[m]==wi) {
            return m;
        }
        if (LWI[m]<wi) {
            l = m+1;
        }
        else {
            r = m-1;
        }
    }
    fprintf(stderr, "LYNDON WORD INDEX NOT FOUND: %li\n", wi);
    assert(0); /* should not reach this point, otherwise word not found */ 
}

unsigned int binomial(unsigned int n, unsigned int k) {
    /* METHOD: from Julia base library, see
     * https://github.com/JuliaLang/julia/blob/master/base/intfuncs.jl     
     */ 
    if (k < 0 || k > n ) {
        return 0;
    }
    if (k == 0 || k == n) {
        return 1;
    }
    if (k == 1) {
        return n;
    }
    if (k > (n>>1)) {
        k = (n - k);
    }
    uint64_t x = n - k +1;
    uint64_t nn = x;
    nn++;
    uint64_t rr = 2;
    while (rr <= k) {
        x = (x*nn) / rr;  /* TODO:  handle possible overflow 
                             (cannot occur with reasonable parameters for BCH) */
        rr++;
        nn++;
    }
    return x;
}

size_t hom_index(size_t K, size_t x[]) {
    size_t i = 0;
    size_t n = 0;
    for (int k=0; k<K; k++) {
        n += x[K-k-1];
        i += binomial(k+n, n-1);
    }
    return i;
}

size_t multi_degree_index(uint8_t K, uint8_t w[], size_t l, size_t r) {
    size_t h[K];
    for (int j=0; j<K; j++) {
        h[j] = 0;
    }
    for (int j=l; j<=r; j++) {
        h[w[j]]++;
    }
    return hom_index(K, h);
}



/* The following two functions are for the generation of Lyndon words
 * and their standard factorizations.
 *
 * METHOD: see J. Sawada, F. Ruskey, Generating Lyndon brackets. 
 * An addendum to: Fast algorithms to generate necklaces, unlabeled necklaces 
 * and irreducible polynomials over GF(2), J. Algorithms 46 (2003) 21–26.a
 *
 * See also Algorithm 2.1 from
 * K. Cattell, F. Ruskey, J. Sawada, M. Serra, C.R. Miers, Fast algorithms 
 * to generate necklaces, unlabeled necklaces and irreducible polynomials over GF(2), 
 * J. Algorithms 37 (2) (2000) 267–282
 */

void genLW(uint8_t K, size_t n, size_t t, size_t p[], 
           uint8_t a[], size_t *wp, size_t split[]) {
    if (t>n) {
        if (p[0]==n) {
            for (int i=0; i<n; i++) {
                W[*wp][i] = a[i+1];
            }
            LWI[*wp] = word_index(K, a, 1, n);
            MDI[*wp] = multi_degree_index(K, a, 1, n);
            if (n>1) {
                size_t m = split[(n-1)*n]; /* split[1,n] */
                size_t wi1 = word_index(K, a, 1, m-1);
                size_t wi2 = word_index(K, a, m, n);
                p1[*wp] = find_lyndon_word_index(0, *wp-1, wi1);
                p2[*wp] = find_lyndon_word_index(0, *wp-1, wi2);
            }
            (*wp)++;
        }
    }
    else {
        size_t q[n];
        for (int i=0; i<n; i++) {
            q[i] = p[i];
        }
        for (int j=a[t-p[0]]; j<K; j++) {
            a[t] = j;
            for (int i=1; i<t; i++) {
                if (a[t]<a[t-p[i-1]]) {
                    p[i-1] = 0;
                }
                if (a[t]>a[t-p[i-1]]) {
                    p[i-1] = t-i+1;
                }
            }
            for (int i=t-1; i>0; i--) {
                if (p[i]==t-i) {
                    split[i+(t-1)*n-1] = i+1;  /* split[i,t] */
                }
                else {
                    split[i+(t-1)*n-1] = split[i+(t-1)*n]; /*split[i, t], split[i+1,t] */
                }
            }
            genLW(K, n, t+1, p, a, wp, split);
            for (int i=0; i<n; i++) {
                p[i] = q[i];
            }
        }
    }
}


void init_lyndon_words(uint8_t K, size_t N) {
    size_t nLW[N];
    number_of_lyndon_words(K, N, nLW);
    size_t mem_len = 0;
    n_lyndon = 0; /* global variable */
    for (int n=1; n<=N; n++) {
        n_lyndon += nLW[n-1];
        mem_len += n*nLW[n-1];
    }
    W = malloc(n_lyndon*sizeof(uint8_t *)); /*TODO check for error */
    p1 = malloc(n_lyndon*sizeof(size_t)); /*TODO check for error */
    p2 = malloc(n_lyndon*sizeof(size_t)); /*TODO check for error */
    nn = malloc(n_lyndon*sizeof(size_t)); /*TODO check for error */
    LWI = malloc(n_lyndon*sizeof(size_t)); /*TODO check for error */
    MDI = malloc(n_lyndon*sizeof(size_t)); /*TODO check for error */
    ii = malloc((N+1)*sizeof(size_t)); /*TODO check for error */
    W[0] = malloc(mem_len*sizeof(uint8_t)); /*TODO check for error */ 
    ii[0] = 0;
    int m=0;
    for (int n=1; n<=N; n++) {
        ii[n] = ii[n-1] + nLW[n-1];
        for (int k=0; k<nLW[n-1]; k++) {            
            W[m+1] = W[m]+n;
            nn[m] = n;
            m++;
        }
    }
    for (int i=0; i<K; i++) {
        p1[i]=i;
        p2[i]=0;
    }

    uint8_t a[N+1];
    size_t p[N];
    size_t split[N*N];
    size_t wp = 0;
    for (int n=1; n<=N; n++) {
        for (int i=0; i<=n; i++) {
            a[i] = 0;
        }
        for (int i=0; i<n; i++) {
            p[i] = 1;
        }
        for (int i=0; i<n*n; i++) {
            split[i] = 0;
        }
        genLW(K, n, 1, p, a, &wp, split);
    }
    assert(wp==n_lyndon);
}

void init_factorial(size_t N) {
    FACTORIAL = malloc((N+1)*sizeof(INTEGER)); /*TODO check for error */
    FACTORIAL[0] = 1;
    for (int n=1; n<=N; n++) {
        FACTORIAL[n] = n*FACTORIAL[n-1];
    }
}

// TODO: free_factorial, free_lyndon_words, free_all, ...


enum expr_type { UNDEFINED, IDENTITY, GENERATOR, SUM, DIFFERENCE, PRODUCT, 
                 COMMUTATOR, TERM, EXPONENTIAL, LOGARITHM };

typedef struct expr {
    enum expr_type type;
    struct expr *arg1;
    struct expr *arg2;
    int num;
    int den;
} expr;

expr* undefined_expr(void) {
    expr *ex = malloc(sizeof(expr));
    ex->type = UNDEFINED;
    ex->arg1 = NULL;
    ex->arg2 = NULL;
    ex->num = 0;
    ex->den = 0;
    return ex;
}

expr* generator(uint8_t n) {
    expr *ex = undefined_expr();
    ex->type = GENERATOR;
    ex->num = n;
    return ex;
}

expr* identity(void) {
    expr *ex = undefined_expr();
    ex->type = IDENTITY;
    return ex;
}

expr* sum(expr* arg1, expr* arg2) {
    expr *ex = undefined_expr();
    ex->type = SUM;
    ex->arg1 = arg1;
    ex->arg2 = arg2;
    return ex;
}

expr* difference(expr* arg1, expr* arg2) {
    expr *ex = undefined_expr();
    ex->type = DIFFERENCE;
    ex->arg1 = arg1;
    ex->arg2 = arg2;
    return ex;
}

expr* product(expr* arg1, expr* arg2) {
    expr *ex = undefined_expr();
    ex->type = PRODUCT;
    ex->arg1 = arg1;
    ex->arg2 = arg2;
    return ex;
}

expr* commutator(expr* arg1, expr* arg2) {
    expr *ex = undefined_expr();
    ex->type = COMMUTATOR;
    ex->arg1 = arg1;
    ex->arg2 = arg2;
    return ex;
}

expr* term(int num, int den, expr* arg) {
    expr *ex = undefined_expr();
    ex->type = TERM;
    ex->arg1 = arg;
    ex->num = num;
    ex->den = den;
    return ex;
}

expr* exponential(expr* arg) {
    expr *ex = undefined_expr();
    ex->type = EXPONENTIAL;
    ex->arg1 = arg;
    return ex;
}

expr* logarithm(expr* arg) {
    expr *ex = undefined_expr();
    ex->type = LOGARITHM;
    ex->arg1 = arg;
    return ex;
}

void print_expr(expr* ex) {
    switch(ex->type) {
        case IDENTITY:
            printf("Id");
            break;
        case GENERATOR: 
            printf("%c", 'A'+ex->num);
            break;
        case SUM:
            printf("(");
            print_expr(ex->arg1);
            printf("+");
            print_expr(ex->arg2);
            printf(")");
            break;
        case DIFFERENCE:
            printf("(");
            print_expr(ex->arg1);
            printf("-");
            print_expr(ex->arg2);
            printf(")");
            break;
        case PRODUCT: 
            print_expr(ex->arg1);
            printf("*");
            print_expr(ex->arg2);
            break;
        case COMMUTATOR: 
            printf("[");
            print_expr(ex->arg1);
            printf(",");
            print_expr(ex->arg2);
            printf("]");
            break;
        case TERM: 
            break;
        case EXPONENTIAL:
            printf("exp(");
            print_expr(ex->arg1);
            printf(")");
            break;
        case LOGARITHM: 
            printf("log(");
            print_expr(ex->arg1);
            printf(")");
            break;
        default:
            fprintf(stderr, "unknown expr type %i\n", ex->type);
            assert(0);
    }
}

int iszero(INTEGER v[], size_t n) {
    for (int j=0; j<n; j++) {
        if (v[j]!=0) {
            return 0;
        }
    }
    return 1;
}


void phi(INTEGER y[], size_t n, uint8_t w[], expr* ex, INTEGER v[]) {
    switch (ex->type) {
        case IDENTITY: 
            for (int j=0; j<=n; j++) {
                y[j] = v[j];
            }
            break;
        case GENERATOR: 
            for (int j=0; j<n; j++) {
                if (w[j]==ex->num) {
                    y[j] = v[j+1];
                }
                else {
                    y[j] = 0;
                }
            }
            y[n] = 0;
            break;
        case SUM: { 
            INTEGER y1[n+1];
            INTEGER y2[n+1];
            phi(y1, n, w, ex->arg1, v);
            phi(y2, n, w, ex->arg2, v);
            for (int j=0; j<=n; j++) {
                y[j] = y1[j] + y2[j];
            }
            } 
            break;
        case DIFFERENCE: {
            INTEGER y1[n+1];
            INTEGER y2[n+1];
            phi(y1, n, w, ex->arg1, v);
            phi(y2, n, w, ex->arg2, v);
            for (int j=0; j<=n; j++) {
                y[j] = y1[j]-y2[j];
            }
            } 
            break;
        case PRODUCT: 
            if (iszero(v, n+1)) {
                return;
            }
            phi(y, n, w, ex->arg2, v);
            if (iszero(y, n+1)) {
                return;
            }
            phi(y, n, w, ex->arg1, y);
            break;
        //case COMMUTATOR: 
        //    break;
        case TERM: 
            phi(y, n, w, ex->arg1, v);
            int p = ex->num;
            int q = ex->den;
            for (int j=1; j<=n; j++) {
                INTEGER h = y[j]*p;
                INTEGER d = h/q;
                if (q*d!=h) {
                    fprintf(stderr, "dividend not divisble by %i\n", q);
                    assert(0);
                }
                y[j] = d;
            }
            break; 
        case EXPONENTIAL: {
            INTEGER z[n+1];
            for (int j=0; j<=n; j++) {
                z[j] = v[j];
                y[j] = v[j];                    
            }
            for (int k=1; k<=n; k++) {
                phi(z, n, w, ex->arg1, z);
                if (iszero(z, n+1)) {
                   return;
                }
                if (k<=20) {
                    long int f = FACTORIAL[k]; /* fits into int => faster arithmetics */
                    for (int j=0; j<=n; j++) {
                        INTEGER d = z[j]/f;
                        if (f*d!=z[j]) {
                           fprintf(stderr, "dividend not divisble by %li\n", f);
                           assert(0);
                        }
                        y[j] += d;
                    }
                }
                else {
                    INTEGER f = FACTORIAL[k];
                    for (int j=0; j<=n; j++) {
                        INTEGER d = z[j]/f;
                        if (f*d!=z[j]) {
                           fprintf(stderr, "dividend not divisble by %li\n", f);
                           assert(0);
                        }
                        y[j] += d;
                    }
                }
            }
            }
            break;
        case LOGARITHM: {
            expr* lm1 = difference(ex->arg1, identity());
            INTEGER z[n+1];
            for (int j=0; j<=n; j++) {
                z[j] = v[j];
                y[j] = v[j];                    
            }
            for (int k=1; k<=n; k++) {
                phi(z, n, w, lm1, z);
                if (iszero(z, n+1)) {
                   return;
                }
                int f = (k%2 ? +1 : -1)*k; /* f = (-1)^(k+1)*k */ 
                for (int j=0; j<=n; j++) {
                    INTEGER d = z[j]/f;
                    if (f*d!=z[j]) {
                       fprintf(stderr, "dividend not divisble by %i\n", f);
                       assert(0);
                    }
                    y[j] += d;
                }
            }
            free(lm1->arg2);
            free(lm1);
            }
            break;
        default:
            fprintf(stderr, "unknown expr type %i\n", ex->type);
            assert(0);
    }
}

void init_lookup_table(uint8_t K, size_t M) {
    lookup_size = M;
    // TODO ...
}


int coeff_word_in_basis_element(uint8_t K, uint8_t w[], size_t l, size_t r, 
           size_t j, size_t H[], size_t W2I[], size_t N) { //, size_t CT[], size_t M) {
    if (l==r) {
        return w[l]==j ? 1 : 0;
    }

    if ((H[l+r*N] != MDI[j]) || (W2I[l+r*N] < LWI[j])) {
        return 0;
    }
    if (W2I[l+r*N] == LWI[j]) {
        return 1;
    }

    size_t j1 = p1[j];
    size_t j2 = p2[j];
    size_t m1 = nn[j1];
    size_t m2 = nn[j2];

    int c2 = coeff_word_in_basis_element(K, w, l+m2, r, j1, H, W2I, N);
    if (c2!=0) {
        c2 *= coeff_word_in_basis_element(K, w, l, l+m2-1, j2, H, W2I, N);
    }

    int c1 = coeff_word_in_basis_element(K, w, l+m1, r, j2, H, W2I, N);
    if (c1!=0) {
        c1 *= coeff_word_in_basis_element(K, w, l, l+m1-1, j1, H, W2I, N);
    }

    return c1 - c2;
}


void coeffs(uint8_t K, size_t N, expr* ex, INTEGER c[], INTEGER denom, int bch_specific) {
    INTEGER e[N+1];

    /* c[0] needs special handling */
    INTEGER t1[2];
    e[0] = 0;
    e[1] = denom;
    phi(t1, 1, W[0], ex, e);
    c[0] = t1[0];

    /* now the other coeffs */
    for (int j=0; j<N; j++){
        e[j] = 0;
    }
    e[N] = denom;

    size_t i1 = ii[N-1];
    size_t i2 = ii[N]-1;

    size_t h1 = MDI[i1];
    size_t h2 = MDI[i2];

    #pragma omp parallel 
    {
    size_t H[N*N];
    size_t W2I[N*N];
    
    for(int l=0; l<=N*N; l++) {
        H[l] = 0;
        W2I[l] = 0;
    }

    size_t JW[N];
    size_t JB[N];
    INTEGER t[N+1];

    #pragma omp for
     //for (int h=h1; h<=h2; h++) {
     for (int h=h2; h>=h1; h--) {
        size_t j1 = 0;
        for (int i=i1; i<=i2; i++) {
            if (MDI[i]==h) {
                if (bch_specific && !(N%2) && p1[i]!=0) {
                    c[i] = 0;
                    continue;
                }
                if (j1==0) {
                    j1 = i;
                }

                uint8_t *w = W[i];
                phi(t, N, w, ex, e);
                c[i] = t[0];

                size_t kW = 0;
                JW[0] = i;
                size_t l = i;
                while (p1[l]==0) {
                    kW++;
                    l = p2[l];
                    JW[kW] = l;
                    c[l] = t[kW];
                }
                for (int l=0; l<N; l++) {
                    for (int r=l; r<N; r++) {
                        H[l + r*N] = multi_degree_index(K, w, l, r); 
                        W2I[l + r*N] = word_index(K, w, l, r); 
                    }
                }

                for (int j=j1; j<=i-1; j++) {
                    if (MDI[j]==h) {
                        size_t kB = 0;
                        JB[0] = j;
                        size_t l = j;
                        while ((kB<kW) && (p1[l]==0)) {
                            kB++;
                            l = p2[l];
                            JB[kB] = l;
                        }
                        INTEGER d = coeff_word_in_basis_element(K, w, kB, N-1, JB[kB], H, W2I, N); //, CT, M)
                        if (d!=0) {
                            for (int l=0; l<=kB; l++) {
                                c[JW[l]] -= d*c[JB[l]];
                            }
                        }
                    }
                }
            }
        }
    }
    }
}



INTEGER gcd(INTEGER a, INTEGER b) {
    while (b!=0) {
       INTEGER t = b; 
       b = a%b; 
       a = t; 
    }
    return abs(a);
}


void init_all(uint8_t K, size_t N) {
    init_factorial(N);
    init_lyndon_words(K, N);
}




int main(void) {
    const size_t N = 12;
    const uint8_t K = 2;


    struct timespec t0, t1;
    double t;

    clock_gettime(CLOCK_MONOTONIC, &t0);	
    
    init_all(K, N);

    clock_gettime(CLOCK_MONOTONIC, &t1);	
    t = (t1.tv_sec-t0.tv_sec) + ( (double) (t1.tv_nsec - t0.tv_nsec))*1e-9;
    printf("initialization: time=%g seconds\n", t );

    expr *A = generator(0);
    expr *B = generator(1);
    expr *BCH = logarithm(product(exponential(A), exponential(B)));
    
    printf("S=");
    print_expr(BCH);
    printf("\n");

    INTEGER denom = FACTORIAL[N]*2*3*5;


    INTEGER *c = malloc(n_lyndon*sizeof(INTEGER));

    clock_gettime(CLOCK_MONOTONIC, &t0);	

/*    
    #pragma omp parallel 
    {
    INTEGER y[N+1];
    INTEGER e[N+1];

    #pragma omp for
    for (int n=0; n<n_lyndon; n++) {
        for (int j=0; j<=nn[n]; j++) {
            e[j] = 0;
        }
        e[nn[n]] = denom;
        phi(y, nn[n], W[n], BCH, e);
        c[n] = y[0]; 
    }
    }
*/    
    coeffs(K, N, BCH, c, denom, 0);

    clock_gettime(CLOCK_MONOTONIC, &t1);	
    t = (t1.tv_sec-t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec)*1e-9;
    printf("coeffs of Lyndon words: time=%g seconds\n", t);
    for (int n=0; n<n_lyndon; n++) {
        printf("%8i  %8li  %8li  %8li  %8li    ", n, p1[n], p2[n], LWI[n], MDI[n]);
        print_word(nn[n], W[n]);
        INTEGER d = gcd(c[n], denom);
        printf(" %8li/%li\n", c[n]/d, denom/d);
    }
    return EXIT_SUCCESS ;
}
