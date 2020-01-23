/* indent -npsl -npcs -br -i4 bch.c */

#include"bch.h"
#include<stdlib.h>
#include<stdint.h>
#include<stdio.h>
#include<assert.h>
#include<time.h>
#ifdef _OPENMP
#include <omp.h>
#endif

static size_t K;             /* number of generators */
static size_t N;             /* maximum length of Lyndon words (=maximum order of Lie series expansion) */
static generator_t **W=NULL; /* W[i] ... nth Lyndon word, ordered primarily by length and secondarily
                                by lexicographical order */
static size_t *p1=NULL;      /* standard factorization of W[i] is W[p1[i]]*W[p2[i]] */
static size_t *p2=NULL;
static size_t *nn=NULL;      /* nn[i] = length of W[i] */
static size_t *ii=NULL;      /* W[ii[n-1]] = first Lyndon word of length n; 
                                W[ii[n]-1] = last Lyndon word of length n */
static size_t *LWI=NULL;     /* LWI[i] = word index of W[i] */
static size_t *MDI=NULL;     /* MDI[i] = multi degree index of W[i] */
static size_t n_lyndon;      /* number of Lyndon words of length <=N, n_lyndon = ii[N] */

static size_t max_lookup_length;
static int **LUT=NULL;
static size_t *LUT_D1=NULL; /* LUT_D1[i] = number of Lyndon words (Lyndon basis elements) 
                               which have multi degree index i */
static size_t *LUT_D2=NULL; /* LUT D2[i] = number of all words of length <= max_lookup_length
                               which have multi degree index i */
static size_t *LUT_P1=NULL; /* Lyndon word W[i] is the LUT_P1[i]-th Lyndon word having 
                               multi degree index MDI[i] */
static size_t *LUT_P2=NULL; /* Word with index i is the LUT_P2[i]-th word in the list of all words 
                               having the same multi degree index as the given word with index i */

static unsigned int verbosity_level;
static INTEGER *FACTORIAL=NULL;


static double tic(void) {
#ifdef _OPENMP
    return omp_get_wtime();
#else
    struct timespec tt;
    clock_gettime(CLOCK_MONOTONIC, &tt);	
    return tt.tv_sec + ((double) tt.tv_nsec)*1e-9;
#endif
}

static double toc(double t0) {
#ifdef _OPENMP
    double t1 = omp_get_wtime();
#else
    struct timespec tt;
    clock_gettime(CLOCK_MONOTONIC, &tt);	
    double t1 = tt.tv_sec + ((double) tt.tv_nsec)*1e-9;
#endif
    return t1-t0;
}

static int ipow(int base, unsigned int exp)
{
    /* computes base^exp 
     * METHOD: see https://stackoverflow.com/questions/101439/the-most-efficient-way-to-implement-an-integer-based-power-function-powint-int
     */
    int result = 1;
    for (;;)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        if (!exp)
            break;
        base *= base;
    }
    return result;
}

static INTEGER gcd(INTEGER a, INTEGER b) {
    /* greatest common divisor of a and b
     * METHOD: Euclid's classical algorithm
     */
    while (b!=0) {
       INTEGER t = b; 
       b = a%b; 
       a = t; 
    }
    return a>=0 ? a : -a;
}

static void moebius_mu(size_t N, int mu[N]) {
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

static void number_of_lyndon_words(generator_t K, size_t N, size_t nLW[N]) {
    /* INPUT: K ... number of letters
     *        N ... maximum lenght of lyndon words
     * OUTPUT: nLW[n] ... number of lyndon words with K letters of length n+1, n=0,...,N-1
     * METHOD: Witt's formula
     */
    int mu[N];
    moebius_mu(N, mu);

    for (int n=1; n<=N; n++) {
        int d = 1;
        int h = 0;
        while (d*d < n) {
            div_t d1r = div(n, d);
            if (d1r.rem==0) {
               int d1 = d1r.quot; 
               h += mu[d-1]*ipow(K, d1)+mu[d1-1]*ipow(K, d);
            }
            d++;
        }
        if (d*d == n) {
            h += mu[d-1]*ipow(K, d);
        }
        nLW[n-1] = h/n;
    }
}

static size_t word_index(size_t K, generator_t w[], size_t l, size_t r) {
    size_t x = 0;
    size_t y = 1;
    for (int j=r; j>= (signed) l; j--) { /* CAUTION! comparison between signed and unsigned */
        x += w[j]*y;
        y *= K;
    }
    return x + (y-1)/(K-1) - 1;
}

static size_t find_lyndon_word_index(size_t l, size_t r, size_t wi) {
    /* METHOD: binary search
     */
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
    fprintf(stderr, "ERROR: Lyndon word index not found: %li\n", wi);
    exit(EXIT_FAILURE);
}

static unsigned int binomial(unsigned int n, unsigned int k) {
    /* binomial coefficient n over k
     * METHOD: from Julia base library, see
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
        x = (x*nn) / rr;  
        rr++;
        nn++;
    }
    return x;
}

static size_t multi_degree_index(size_t K, generator_t w[], size_t l, size_t r) {
    size_t h[K];
    for (int j=0; j<K; j++) {
        h[j] = 0;
    }
    for (int j=l; j<=r; j++) {
        h[w[j]]++;
    }
    size_t index = 0;
    size_t n = 0;
    for (int k=0; k<K; k++) {
        n += h[K-k-1];
        index += binomial(k+n, n-1);
    }
    return index;
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

static void genLW(size_t K, size_t n, size_t t, size_t p[], 
           generator_t a[], size_t *wp, size_t split[]) {
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

static void init_lyndon_words(void) {
    double t0 = tic();
    size_t nLW[N];
    number_of_lyndon_words(K, N, nLW);
    size_t mem_len = 0;
    n_lyndon = 0;
    for (int n=1; n<=N; n++) {
        n_lyndon += nLW[n-1];
        mem_len += n*nLW[n-1];
    }
    W = malloc(n_lyndon*sizeof(generator_t *)); 
    p1 = malloc(n_lyndon*sizeof(size_t)); 
    p2 = malloc(n_lyndon*sizeof(size_t)); 
    nn = malloc(n_lyndon*sizeof(size_t)); 
    LWI = malloc(n_lyndon*sizeof(size_t));
    MDI = malloc(n_lyndon*sizeof(size_t));
    ii = malloc((N+1)*sizeof(size_t)); 
    W[0] = malloc(mem_len*sizeof(generator_t)); 
    ii[0] = 0;
    int m=0;
    for (int n=1; n<=N; n++) {
        ii[n] = ii[n-1] + nLW[n-1];
        for (int k=0; k<nLW[n-1]; k++) {            
            if (m<n_lyndon-1) { /* avoiding illegal W[n_lyndon] */
                W[m+1] = W[m]+n;
            }
            nn[m] = n;
            m++;
        }
    }
    assert(m==n_lyndon);
    for (int i=0; i<K; i++) {
        p1[i]=i;
        p2[i]=0;
    }

    generator_t a[N+1];
    size_t p[N];
    size_t split[N*N];
    size_t wp = 0;
    for (int n=1; n<=N; n++) {
        for (int i=0; i<=n; i++) a[i] = 0; 
        for (int i=0; i<n; i++) p[i] = 1; 
        for (int i=0; i<n*n; i++) split[i] = 0; 
        genLW(K, n, 1, p, a, &wp, split);
    }
    assert(wp==n_lyndon);
    if (verbosity_level>=1) {
        double t1 = toc(t0);
        printf("#number of Lyndon words of length<=%li over set of %li letters: %li\n", N, K, n_lyndon);
        printf("#init Lyndon words: time=%g sec\n", t1);
    }
}

static void free_lyndon_words(void) {
    free(W[0]);
    free(W);
    free(nn);
    free(ii);
    free(LWI);
    free(MDI);
    /* Note: p1 and p2 are taken over by a lie_series_t struct
       and are eventually freed by free_lie_series */
}

static void init_factorial(void) {
    FACTORIAL = malloc((N+1)*sizeof(INTEGER)); 
    FACTORIAL[0] = 1;
    for (int n=1; n<=N; n++) {
        FACTORIAL[n] = n*FACTORIAL[n-1];
    }
}

static void free_factorial(void) {
    free(FACTORIAL);
}


static expr_t* undefined_expr(void) {
    expr_t *ex = malloc(sizeof(expr_t));
    ex->type = UNDEFINED;
    ex->arg1 = NULL;
    ex->arg2 = NULL;
    ex->num = 0;
    ex->den = 0;
    return ex;
}

expr_t* identity(void) {
    expr_t *ex = undefined_expr();
    ex->type = IDENTITY;
    return ex;
}

expr_t* generator(generator_t n) {
    expr_t *ex = undefined_expr();
    ex->type = GENERATOR;
    ex->num = n;
    return ex;
}

expr_t* sum(expr_t* arg1, expr_t* arg2) {
    expr_t *ex = undefined_expr();
    ex->type = SUM;
    ex->arg1 = arg1;
    ex->arg2 = arg2;
    return ex;
}

expr_t* difference(expr_t* arg1, expr_t* arg2) {
    expr_t *ex = undefined_expr();
    ex->type = DIFFERENCE;
    ex->arg1 = arg1;
    ex->arg2 = arg2;
    return ex;
}

expr_t* product(expr_t* arg1, expr_t* arg2) {
    expr_t *ex = undefined_expr();
    ex->type = PRODUCT;
    ex->arg1 = arg1;
    ex->arg2 = arg2;
    return ex;
}

expr_t* negation(expr_t* arg) {
    expr_t *ex = undefined_expr();
    ex->type = NEGATION;
    ex->arg1 = arg;
    return ex;
}

expr_t* term(int num, int den, expr_t* arg) {
    expr_t *ex = undefined_expr();
    ex->type = TERM;
    ex->arg1 = arg;
    ex->num = num;
    ex->den = den;
    return ex;
}

expr_t* exponential(expr_t* arg) {
    expr_t *ex = undefined_expr();
    ex->type = EXPONENTIAL;
    ex->arg1 = arg;
    return ex;
}

expr_t* logarithm(expr_t* arg) {
    expr_t *ex = undefined_expr();
    ex->type = LOGARITHM;
    ex->arg1 = arg;
    return ex;
}

expr_t* commutator(expr_t* arg1, expr_t* arg2) {
    return difference(product(arg1, arg2), 
                      product(arg2, arg1));
}


void free_expr(expr_t* ex) {
    if (ex) {
        free(ex->arg1);
        free(ex->arg2);
        free(ex);
    }
}    

void print_expr(expr_t* ex) {
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
        case NEGATION: 
            printf("(-1)*");
            print_expr(ex->arg1);
            break;
        case TERM: 
            printf("(%i/%i)*", ex->num, ex->den);
            print_expr(ex->arg1);
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
            fprintf(stderr, "ERROR: unknown expr type %i\n", ex->type);
            exit(EXIT_FAILURE);
    }
}

static inline int iszero(INTEGER v[], size_t n) {
    for (int j=0; j<n; j++) {
        if (v[j]!=0) {
            return 0;
        }
    }
    return 1;
}

static inline void check_for_divisibility_by_int(INTEGER p, int q, INTEGER d) {
#ifndef NO_DIVISIBILITY_CHECKS    
    if (q*d!=p) {
        int q1 = (q>0?q:-q)/gcd(p,q);
        fprintf(stderr, "ERROR: dividend not divisble by %i\n", q1);
        exit(EXIT_FAILURE);
    }
#endif    
}

static inline void check_for_divisibility_by_long_int(INTEGER p, long int q, INTEGER d) {
#ifndef NO_DIVISIBILITY_CHECKS    
    if (q*d!=p) {
        long int q1 = (q>0?q:-q)/gcd(p,q);
        fprintf(stderr, "ERROR: dividend not divisble by %li\n", q1);
        exit(EXIT_FAILURE);
    }
#endif    
}

static inline void check_for_divisibility_by_INTEGER(INTEGER p, INTEGER q, INTEGER d) {
#ifndef NO_DIVISIBILITY_CHECKS    
    if (q*d!=p) {
        long int q1 = (q>0?q:-q)/gcd(p,q);
        fprintf(stderr, "ERROR: dividend not divisble by %li\n", q1);
        exit(EXIT_FAILURE);
    }
#endif    
}

static void phi(INTEGER y[], size_t n, generator_t w[], expr_t* ex, INTEGER v[]) {
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
                for (int j=0; j<n; j++) { 
                    y[j] = 0;
                }
                return;
            }
            phi(y, n, w, ex->arg2, v);
            if (iszero(y, n+1)) {
                return;
            }
            phi(y, n, w, ex->arg1, y);
            break;
        case NEGATION: 
            phi(y, n, w, ex->arg1, v);
            for (int j=0; j<n; j++) {
                y[j] = -y[j];
            }
            break;
        case TERM: 
            phi(y, n, w, ex->arg1, v);
            int p = ex->num;
            int q = ex->den;
            for (int j=0; j<n; j++) {
                INTEGER h = y[j]*p;
                INTEGER d = h/q;
                check_for_divisibility_by_int(h, q, d);
                y[j] = d;
            }
            break; 
        case EXPONENTIAL: {
            INTEGER z[n+1];
            for (int j=0; j<=n; j++) {
                z[j] = v[j];
                y[j] = v[j];                    
            }
            if (iszero(z, n+1)) {
                return;
            }
            for (int k=1; k<=n; k++) {
                phi(z, n, w, ex->arg1, z);
                if (iszero(z, n+1)) {
                   return;
                }
                if (k<=20) {
                    long int f = FACTORIAL[k]; /* fits into long int => faster execution expected */
                    for (int j=0; j<=n; j++) {
                        INTEGER d = z[j]/f;
                        check_for_divisibility_by_long_int(z[j], f, d);
                        y[j] += d;
                    }
                }
                else {
                    INTEGER f = FACTORIAL[k];
                    for (int j=0; j<=n; j++) {
                        INTEGER d = z[j]/f;
                        check_for_divisibility_by_INTEGER(z[j], f, d);
                        y[j] += d;
                    }
                }
            }
            }
            break;
        case LOGARITHM: {
            INTEGER z[n+1];
            for (int j=0; j<=n; j++) {
                z[j] = v[j];
                y[j] = v[j];                    
            } 
            if (iszero(z, n+1)) {
                return;
            }
            INTEGER h[n+1];
            for (int k=1; k<=n; k++) {
                for (int j=0; j<=n; j++) {
                    h[j] = z[j];
                }
                phi(z, n, w, ex->arg1, z);
                for (int j=0; j<=n; j++) {
                    z[j] -= h[j];
                }
                if (iszero(z, n+1)) {
                   return;
                }
                int f = (k%2 ? +1 : -1)*k; /* f = (-1)^(k+1)*k */ 
                for (int j=0; j<=n; j++) {
                    INTEGER d = z[j]/f;
                    check_for_divisibility_by_int(z[j], f, d);
                    y[j] += d;
                }
            }
            }
            break;
        default:
            fprintf(stderr, "ERROR: unknown expr type %i\n", ex->type);
            exit(EXIT_FAILURE);
    }
}

static int coeff_word_in_basis_element(size_t l, size_t r, size_t j, size_t D2I[], size_t W2I[]) { 
    
    size_t di = D2I[l + r*N];
    if (di != MDI[j]) {
        return 0;  /* multi-degrees don't match */
    }

    size_t wi = W2I[l + r*N];
    if (r-l+1<=max_lookup_length) {  /* use lookup table */
        return LUT[di][LUT_P1[j] + LUT_P2[wi]*LUT_D1[di]];
    }

    if (wi < LWI[j]) {
        return 0;
    }
    if (wi == LWI[j]) {
        return 1;
    }

    size_t j1 = p1[j];
    size_t j2 = p2[j];
    size_t m1 = nn[j1];
    size_t m2 = nn[j2];

    int c2 = coeff_word_in_basis_element(l+m2, r, j1, D2I, W2I);
    if (c2!=0) {
        c2 *= coeff_word_in_basis_element(l, l+m2-1, j2, D2I, W2I);
    }

    int c1 = coeff_word_in_basis_element(l+m1, r, j2, D2I, W2I);
    if (c1!=0) {
        c1 *= coeff_word_in_basis_element(l, l+m1-1, j1, D2I, W2I);
    }

    return c1 - c2;
}

static void gen_ith_word_of_length_n(size_t i, size_t n, generator_t w[]) {
    /* METHOD: compute base K expansion of i */
    for (int j=0; j<n; j++) {
        w[j] = 0;
    }
    size_t k=n-1;
    while (i>0) {
        w[k] = i%K;
        i/=K;
        k--;
    }
}

static void init_lookup_table(size_t M) {
    if (M==0) {
        max_lookup_length = M;
        return;
    }
    double t0 = tic();
    size_t H = MDI[ii[M]-1]+1; 
    LUT_D1 = calloc(H, sizeof(size_t));
    LUT_P1 = calloc(ii[M], sizeof(size_t));
    for (int i=0; i<ii[M]; i++) {
        LUT_P1[i] = LUT_D1[MDI[i]];
        LUT_D1[MDI[i]]++;
    }
    LUT_D2 = calloc(H, sizeof(size_t));
    LUT_P2 = calloc((ipow(K, M+1)-1)/(K-1)-1, sizeof(size_t));
    generator_t w[M];
    for (int n=1; n<=M; n++) {
        for (int i=0; i<ipow(K, n); i++) {
            gen_ith_word_of_length_n(i, n, w);
            size_t wi = word_index(K, w, 0, n-1);
            size_t di = multi_degree_index(K, w, 0, n-1);
            if (di<H) { /* this holds for all di except the last one */
               LUT_P2[wi] = LUT_D2[di];
               LUT_D2[di]++;
            }
        }
    }
    LUT = calloc(H, sizeof(size_t*));
    for (int h=0; h<H; h++) {
        size_t d = LUT_D1[h]*LUT_D2[h];
        if (d>0) {
            LUT[h] = calloc(d, sizeof(int));
        }
    }

    for (int n=1; n<=M; n++) {
        size_t i1 = ii[n-1];
        size_t i2 = ii[n]-1;

        max_lookup_length = n-1;

        #pragma omp parallel 
        {
        size_t D2I[N*N];
        size_t W2I[N*N];
        generator_t w[N];
        
        #pragma omp for schedule(dynamic,1)
        for (int i=0; i<ipow(K, n); i++) {
            gen_ith_word_of_length_n(i, n, w);

            for (int l=0; l<n; l++) {
                for (int r=l; r<n; r++) {
                    D2I[l + r*N] = multi_degree_index(K, w, l, r); 
                    W2I[l + r*N] = word_index(K, w, l, r); 
                }
            }
            size_t di = D2I[0 +(n-1)*N];
            size_t wi = W2I[0 +(n-1)*N];

            for (int j=i1; j<=i2; j++) {
                if (MDI[j]==di) {
                    int c = coeff_word_in_basis_element(0, n-1, j, D2I, W2I); 
                    LUT[di][LUT_P1[j] + LUT_P2[wi]*LUT_D1[di]] = c;
                }
            }
        }
        }
    }
    max_lookup_length = M;
    if (verbosity_level>=1) {
        double t1 = toc(t0);
        printf("#lookup table for word lengths<=%li\n", M);
        printf("#init lookup table: time=%g sec\n", t1);
    }
}

static void free_lookup_table(void) {
    free(LUT);
    free(LUT_D1);
    free(LUT_D2);
    free(LUT_P1);
    free(LUT_P2);
}

static inline size_t get_right_factors(size_t i, size_t J[], size_t kmax) {
    size_t k = 0;
    J[0] = i;
    size_t l = i;
    while ((k<kmax) && (p1[l]==0)) {
        k++;
        l = p2[l];
        J[k] = l;
    }
    return k;
}

static void compute_lie_series(expr_t* ex, INTEGER c[], INTEGER denom, int shortcut_for_classical_bch) {
    if (verbosity_level>=1) {
        printf("#expression="); print_expr(ex); printf("\n"); 
        printf("#denominator="); print_INTEGER(denom); printf("\n");
        printf("#divisibility checks are "
#ifdef NO_DIVISIBILITY_CHECKS    
            "off"
#else
            "on"
#endif
        "\n");
    }
    double t0 = tic();

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
    size_t D2I[N*N];
    size_t W2I[N*N];
    
    for(int l=0; l<=N*N; l++) {
        D2I[l] = 0;
        W2I[l] = 0;
    }

    size_t JW[N];
    size_t JB[N];
    INTEGER t[N+1];

    /* Note: We choose schedule(dynamic, 1) because each
     * iteration of the loop is associated with a specific 
     * multi degree index, and the work to be done varies widely
     * for different multi degree indices. 
     */
    #pragma omp for schedule(dynamic,1) 
    for (int h=h1; h<=h2; h++) {
        size_t j1 = 0;
        for (int i=i1; i<=i2; i++) {
            if (MDI[i]==h) {
                if (shortcut_for_classical_bch && !(N%2) && p1[i]!=0) {
                    c[i] = 0;
                    continue;
                }
                if (j1==0) {
                    j1 = i;
                }

                generator_t *w = W[i];
                phi(t, N, w, ex, e);

                size_t kW = get_right_factors(i, JW, N);
                for (int k=0; k<=kW; k++) {
                    c[JW[k]] = t[k];
                }

                for (int l=0; l<N; l++) {
                    for (int r=l; r<N; r++) {
                        D2I[l + r*N] = multi_degree_index(K, w, l, r); 
                        W2I[l + r*N] = word_index(K, w, l, r); 
                    }
                }

                for (int j=j1; j<=i-1; j++) {
                    if (MDI[j]==h) {
                        size_t kB = get_right_factors(j, JB, kW);
                        int d = coeff_word_in_basis_element(kB, N-1, JB[kB], D2I, W2I); 
                        if (d!=0) {
                            for (int k=0; k<=kB; k++) {
                                c[JW[k]] -= d*c[JB[k]];
                            }
                        }
                    }
                }
            }
        }
    }
    }
    if (verbosity_level>=1) {
        double t1 = toc(t0);
        printf("#compute lie series: time=%g sec\n", t1);
    }
}

/* table den_fac obtained with the following Julia code:
n = 33
F = [factorial(Int128(k)) for k=0:n-1]
M = zeros(Int128,n,n)
M[:,1] = F
for m = 2:n
    M[m+1:end,m] = [lcm([F[k]*M[n-k+1,m-1] for k=2:n-m+1]) for n=m+1:n]  
end
using LinearAlgebra # for diagm
M *= diagm(1:n)
D = [lcm(M[k,1:k-1]) for k=1:n]
den_fac = [div(D[i],F[i]) for i=1:n]
 */

static int den_fac[33] = {1, 1, 1, 2, 1, 6, 2, 6, 3, 10, 2, 6, 2, 210, 30, 12, 3, 30, 10, 
                          210, 42, 330, 30, 60, 30, 546, 42, 28, 2, 60, 4, 924, 231};

static void init_all(size_t number_of_generators, size_t order, size_t max_lookup_length) {
    K = number_of_generators;
    N = order;
    init_factorial();
    init_lyndon_words();
    init_lookup_table(max_lookup_length);
}

static void free_all(void) {
    free_factorial();
    free_lookup_table();
    free_lyndon_words();
}

static lie_series_t gen_result(INTEGER *c, INTEGER denom) {
    lie_series_t LS;
    LS.K = K;
    LS.N = N;
    LS.n_lyndon = n_lyndon;
    LS.p1 = p1;
    LS.p2 = p2;
    LS.denom = denom;
    LS.c = c;
    return LS;
}

lie_series_t lie_series(size_t K, expr_t* expr, size_t N, int64_t fac, size_t M) {
    double t0 = tic();
    init_all(K, N, M);
    INTEGER *c = malloc(n_lyndon*sizeof(INTEGER));
    INTEGER denom = FACTORIAL[N]*den_fac[N]*fac;
    compute_lie_series(expr, c, denom, 0);
    lie_series_t LS = gen_result(c, denom);
    free_all();
    if (verbosity_level>=1) {
        double t1 = toc(t0);
        printf("#total time=%g sec\n", t1);
    }
    return LS;
}

lie_series_t BCH(size_t N, size_t M) {
    double t0 = tic();
    expr_t *A = generator(0);
    expr_t *B = generator(1);
    expr_t *expr = logarithm(product(exponential(A), exponential(B)));
    init_all(2, N, M);
    INTEGER *c = malloc(n_lyndon*sizeof(INTEGER));
    INTEGER denom = FACTORIAL[N]*den_fac[N];
    compute_lie_series(expr, c, denom, 1);
    lie_series_t LS = gen_result(c, denom);
    free_all();
    free_expr(A);
    free_expr(B);
    free_expr(expr);
    if (verbosity_level>=1) {
        double t1 = toc(t0);
        printf("#total time=%g sec\n", t1);
    }
    return LS;
}

lie_series_t symBCH(size_t N, size_t M) {
    double t0 = tic();
    expr_t *halfA = generator(0);
    expr_t *B = generator(1);
    expr_t *expr = logarithm(product(product(exponential(halfA), exponential(B)), 
                                     exponential(halfA)));
    init_all(2, N, M);
    INTEGER *c = malloc(n_lyndon*sizeof(INTEGER));
    INTEGER denom = FACTORIAL[N]*den_fac[N];
    if (verbosity_level>=1) {
        printf("#NOTE: in the following expression, A stands for A/2\n");
    }
    compute_lie_series(expr, c, denom, 0);
    lie_series_t LS = gen_result(c, denom);
    for (int i=0; i<n_lyndon; i++) {
        int nA = get_degree_of_generator(&LS, i, 0);
        LS.c[i] <<= N-1-nA; /* c[i] = c[i]*2^(N-1-nA) */
    }
    LS.denom <<= N-1; /* denom = denom*2^(N-1) */
    if (verbosity_level>=1) {
        printf("#denominator changed to "); print_INTEGER(LS.denom); printf("\n");
    }
    free_all();
    free_expr(halfA);
    free_expr(B);
    free_expr(expr);
    if (verbosity_level>=1) {
        double t1 = toc(t0);
        printf("#total time=%g sec\n", t1);
    }
    return LS;
}


void free_lie_series(lie_series_t LS) {
    free(LS.p1);
    free(LS.p2);
    free(LS.c);
}


void set_verbosity_level(unsigned int level) {
    verbosity_level = level;
}

//void set_max_lookup_table_length(size_t size) {
//}

void print_word(lie_series_t *LS,  size_t i) {
    if (i<LS->K) {
        printf("%c", (char) ('A'+i));
    }
    else {
        print_word(LS, LS->p1[i]);
        print_word(LS, LS->p2[i]);
    }
}   

void print_basis_element(lie_series_t *LS,  size_t i) {
    if (i<LS->K) {
        printf("%c", (char) ('A'+i));
    }
    else {
        printf("[");
        print_basis_element(LS, LS->p1[i]);
        printf(",");
        print_basis_element(LS, LS->p2[i]);
        printf("]");
    }
}


#ifdef USE_INT128_T
void print_INTEGER(__int128_t x) {
    int s = 1;
    if (x<0) {
        s = -1;
        x = -x;
    }
    uint64_t F = 100000000000000000ULL;
    int64_t x1 = x % F;
    x /=F;
    if (x>0) {
        int64_t x2 = x % F;
        x /= F;
        if (x>0) {
            int64_t x3 = x;
            printf("%li%017li%017li",s*x3,x2,x1);
        }
        else {
            printf("%li%017li",s*x2,x1);
        }
    }
    else {
        printf("%li",s*x1);
    }
}
#else
void print_INTEGER(int64_t x) {
    printf("%li",x);
}
#endif

void print_lie_series(lie_series_t *LS) {
    for (int i=0; i<LS->n_lyndon; i++) {
        if (LS->c[i]!=0) {
            INTEGER d = gcd(LS->c[i], LS->denom);
            INTEGER p = LS->c[i]/d;
            INTEGER q = LS->denom/d;
            if (p>0) {
                printf("+");
            }
            print_INTEGER(p);
            printf("/");
            print_INTEGER(q);
            printf("*");
            print_basis_element(LS, i);
        }
    }
}

int get_degree(lie_series_t *LS, size_t i) {
    if (i<LS->K) {
        return 1;
    }
    else {
        return get_degree(LS, LS->p1[i])+get_degree(LS, LS->p2[i]);
    }
}

int get_degree_of_generator(lie_series_t *LS, size_t i, uint8_t g) {
    if (i<LS->K) {
        return i==g ? 1 : 0;
    }
    else {
        return get_degree_of_generator(LS, LS->p1[i], g)
              +get_degree_of_generator(LS, LS->p2[i], g);
    }
}

void print_lists(lie_series_t *LS, unsigned int what) {
    if (verbosity_level>=1) {
        printf("# ");
        if (what & PRINT_INDEX) printf("i");
        if (what & PRINT_DEGREE) printf("\t|i|");
        if (what & PRINT_MULTI_DEGREE) printf("\tmulti degree"); 
        if (what & PRINT_FACTORS) printf("\ti'\ti\"");
        if (what & PRINT_WORD) printf("\tword");
        if (what & PRINT_BASIS_ELEMENT) printf("\tbasis element");
        if (what & PRINT_COEFFICIENT) printf("\tcoefficient"); 
        printf("\n");
    }
    for (int i=0; i<LS->n_lyndon; i++) {
        if (what & PRINT_INDEX) printf("%i", i);
        if (what & PRINT_DEGREE) printf("\t%i", get_degree(LS, i));
        if (what & PRINT_MULTI_DEGREE) {
            printf("\t(%i", get_degree_of_generator(LS, i, 0));
            for (int g=1; g<LS->K; g++) {
                printf(",%i", get_degree_of_generator(LS, i, g));
            }
            printf(")");
        }
        if (what & PRINT_FACTORS) printf("\t%li\t%li", LS->p1[i], LS->p2[i]);
        if (what & PRINT_WORD) {
            printf("\t");
            print_word(LS, i);
        }
        if (what & PRINT_BASIS_ELEMENT) {
            printf("\t");
            print_basis_element(LS, i);

        }
        if (what & PRINT_COEFFICIENT) {
            INTEGER d = gcd(LS->c[i], LS->denom);
            INTEGER p = LS->c[i]/d;
            INTEGER q = LS->denom/d;
            printf("\t");
            print_INTEGER(p);
            printf("/");
            print_INTEGER(q);
        }
        printf("\n");
    }
}



