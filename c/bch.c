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
static generator_t **W=NULL; /* W[i] ... nth Lyndon word, ordered primarily by length and 
                                secondarily by lexicographical order */
static uint32_t *p1=NULL;    /* standard factorization of W[i] is W[p1[i]]*W[p2[i]] */
static uint32_t *p2=NULL;
static uint8_t  *nn=NULL;    /* nn[i] = length of W[i] */
static uint32_t *ii=NULL;    /* W[ii[n-1]] = first Lyndon word of length n; 
                                W[ii[n]-1] = last Lyndon word of length n */
static uint32_t *WI=NULL;    /* WI[i] = word index of W[i] */
static uint32_t *DI=NULL;    /* DI[i] = multi degree index of W[i] */




static size_t N_LYNDON;      /* number of Lyndon words of length <=N, N_LYNDON = ii[N] */

static size_t M = 0;             /* maximum lookup length */ 

typedef int32_t TINT_t ;
static TINT_t **T = NULL;       /* precomputed lookup table: word with index i has coefficient 
                                T[i][T_P[j]]  in basis element with number j.  */
static uint32_t *T_P = NULL;

static unsigned int VERBOSITY_LEVEL = 0;

#ifdef _OPENMP
static unsigned int INNER_THREADS = 1;
static unsigned int OUTER_THREADS = 1; 
#endif

static INTEGER *FACTORIAL=NULL;

/*
static uint32_t *DIABBB=NULL;    // DIB[n] =  DI[ii[n]-1] multi degree index of ABBBBBB, #B = n-1 
static int *SBINOMIAL=NULL;
*/


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

static int ipow(int base, unsigned int exp) {
    /* computes base^exp 
     * METHOD: see https://stackoverflow.com/questions/101439/the-most-efficient-way-to-implement-an-integer-based-power-function-powint-int
     */
    if (base==2) {
        return 2<<(exp-1);
    }
    else {
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
}

static INTEGER gcd(INTEGER a, INTEGER b) {
    /* computes greatest common divisor of a and b
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
    /* computes the index of the subword w[l:r] of w starting at position l and
     * ending at position r. The index is given as w[l:r] interpreted as a K-adic
     * number plus the number (K^n-1)/(K-1)-1 of words of length < n, where 
     * n = r-l+1 = length of w[l:r] 
     */
    size_t x = 0;
    size_t y = 1;
    if (K==2) {
        for (int j=r; j>= (signed) l; j--) { /* CAUTION! comparison between signed and unsigned */
            x += w[j]*y;
            y <<= 1;
        }
        return x + y - 2;
    }
    else {
        for (int j=r; j>= (signed) l; j--) { /* CAUTION! comparison between signed and unsigned */
            x += w[j]*y;
            y *= K;
        }
        return x + (y-1)/(K-1) - 1;
    }
}

static size_t find_lyndon_word_index(size_t l, size_t r, size_t wi) {
    /* finds index wi in the sorted list of indices WI. Start search at position l 
     * and stop * it at position r. This function is only applied in situations where 
     * the search will not fail.
     * METHOD: binary search
     */
    while (l<=r) {
        size_t m = l + (r-l)/2;
        if (WI[m]==wi) {
            return m;
        }
        if (WI[m]<wi) {
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
    /* computes binomial coefficient n over k
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

static size_t tuple(size_t K, size_t h[]) {
    if (K==2) {
        int s = h[0]+h[1];
        return ((s*(s+1))>>1)+h[1];
    }
    else {
        size_t index = 0;
        size_t n = 0;
        for (int k=0; k<K; k++) {
            n += h[K-k-1];
            index += binomial(k+n, n-1);
        }
        return index;
    }
}

static size_t multi_degree_index(size_t K, generator_t w[], size_t l, size_t r) {
    size_t h[K];
    for (int j=0; j<K; j++) {
        h[j] = 0;
    }
    for (int j=l; j<=r; j++) {
        h[w[j]]++;
    }
    return tuple(K, h); 
}

static void gen_D(size_t K, size_t N, generator_t w[], size_t D[]) {
    size_t h[K];
    for (int r=N-1; r>=0; r--) {
        for (int j=0; j<K; j++) {
            h[j] = 0;
        }
        for (int l=r; l>=0; l--) {
            h[w[l]]++;
            D[l + r*N] = tuple(K, h);
        }
    }
}


static void gen_TWI(size_t K, size_t N, size_t M, generator_t w[], TINT_t **TWI) {
    for (int r=N-1; r>=0; r--) {
        int x = 0;
        int y = 1;
        if (K==2) {
            for (int l=r; l>=0 && l>r-(signed) M; l--) {
                x += w[l]*y;
                y <<= 1;
                TWI[l + r*N] = T[x + y - 2]; 
            }
        }
        else {
            int os = 0;
            for (int l=r; l>=0 && l>r-(signed) M; l--) {
                x += w[l]*y;
                y *= K;
                TWI[l + r*N] = T[x + os]; 
                os += y;
            }
        }
    }
}

static int longest_right_lyndon_factor(generator_t w[], size_t l, size_t r) {
/* returns starting position of the longest right Lyndon factor of the subword w[l:r]
 * METHOD: based on the algorithm MaxLyn from
 *   F. Franek, A. S. M. S. Islam, M. S. Rahman, W. F. Smyth: Algorithms to Compute the Lyndon Array. 
 *   Stringology 2016: 172-184
 */
    for (int j=l+1; j<r; j++) {        
        int i = j+1;
        while (i <= r) {
            int k = 0;
            while ((i+k <= r) && (w[j+k]==w[i+k])) {
                k += 1;
            } 
            if ((i+k > r) || (w[j+k] >= w[i+k])) {
                break;
            }
            else {
                i += k + 1;
            }
        }
        if (i==r+1) {
            return j;
        }
    }
    return r;
}

/* The following two functions are for the generation of Lyndon words.
 * METHOD: Algorithm 2.1 from
 *   K. Cattell, F. Ruskey, J. Sawada, M. Serra, C.R. Miers, Fast algorithms 
 *   to generate necklaces, unlabeled necklaces and irreducible polynomials over GF(2), 
 *   J. Algorithms 37 (2) (2000) 267–282
 */

static void genLW(size_t K, size_t n, size_t t, size_t p, generator_t a[], size_t wp[]) {
    if (t>n) {
        if (p==n) {
            int H = 0;
            size_t j2;
            while ((longest_right_lyndon_factor(a, H+1, n)==H+2) && (a[H+1]==0)) { 
                H++;
            }
            for (int h=H; h>=0; h--)  {
                size_t n0 = n-h;
                size_t j = wp[n0-1];
                for (int i=0; i<n0; i++) {
                    W[j][i] = a[i+h+1];
                }
                WI[j] = word_index(K, a, h+1, n);
                DI[j] = multi_degree_index(K, a, h+1, n);
                if (n0>1) {
                    if (h<H) {
                        p1[j] = 0;
                        p2[j] = j2;
                    }
                    else {
                        size_t m = longest_right_lyndon_factor(a, h+1, n);
                        size_t wi1 = word_index(K, a, h+1, m-1);
                        size_t wi2 = word_index(K, a, m, n);
                        int n1 = m-h-1;
                        int n2 = n0-n1;
                        p1[j] = find_lyndon_word_index(ii[n1-1], wp[n1-1], wi1);
                        p2[j] = find_lyndon_word_index(ii[n2-1], wp[n2-1], wi2);
                    }
                }
                j2 = j;
                wp[n0-1]++;
            } 
        }
    }
    else {
        a[t] = a[t-p];
        genLW(K, n, t+1, p, a, wp); 
        for (int j=a[t-p]+1; j<K; j++) {
             a[t] = j;
             genLW(K, n, t+1, t, a, wp);
        }
    }
}

static void init_lyndon_words(void) {
    double t0 = tic();
    size_t nLW[N];
    number_of_lyndon_words(K, N, nLW);
    size_t mem_len = 0;
    N_LYNDON = 0;
    for (int n=1; n<=N; n++) {
        N_LYNDON += nLW[n-1];
        mem_len += n*nLW[n-1];
    }
    W = malloc(N_LYNDON*sizeof(generator_t *)); 
    p1 = malloc(N_LYNDON*sizeof(uint32_t)); 
    p2 = malloc(N_LYNDON*sizeof(uint32_t)); 
    nn = malloc(N_LYNDON*sizeof(uint8_t)); 
    WI = malloc(N_LYNDON*sizeof(uint32_t));
    DI = malloc(N_LYNDON*sizeof(uint32_t));
    ii = malloc((N+1)*sizeof(uint32_t)); 
    W[0] = malloc(mem_len*sizeof(generator_t)); 
    ii[0] = 0;
    int m=0;
    for (int n=1; n<=N; n++) {
        ii[n] = ii[n-1] + nLW[n-1];
        for (int k=0; k<nLW[n-1]; k++) {            
            if (m<N_LYNDON-1) { /* avoiding illegal W[N_LYNDON] */
                W[m+1] = W[m]+n;
            }
            nn[m] = n;
            m++;
        }
    }
    assert(m==N_LYNDON);
    for (int i=0; i<K; i++) {
        p1[i] = i;
        p2[i] = 0;
    }

    generator_t a[N+1];
    size_t wp[N];
    for (int i=0; i<N; i++) {
        wp[i] = ii[i]; 
    }
    wp[0] = 1;
    W[0][0] = 0;
    WI[0] = 0;
    DI[0] = 1;

    for (int i=0; i<=N; i++) {
        a[i] = 0; 
    }

    genLW(K, N, 1, 1, a, wp);

/*
    DIABBB = malloc(N*sizeof(uint32_t)); 
    for (int n=1; n<N; n++) {
       DIABBB[n] =  DI[ii[n]-1];
    }
*/    
    
    if (VERBOSITY_LEVEL>=1) {
        double t1 = toc(t0);
        printf("#number of Lyndon words of length<=%li over set of %li letters: %li\n", N, K, N_LYNDON);
        printf("#init Lyndon words: time=%g sec\n", t1);
        if (VERBOSITY_LEVEL>=2) {
            fflush(stdout);
        }
    }
}

static void free_lyndon_words(void) {
    free(W[0]);
    free(W);
    free(nn);
    free(ii);
    free(WI);
    free(DI);
    /* Note: p1 and p2 are taken over by a lie_series_t struct
       and are eventually freed by free_lie_series */
}

static void init_factorial(void) {
    FACTORIAL = malloc((N+1)*sizeof(INTEGER)); 
    FACTORIAL[0] = 1;
    for (int n=1; n<=N; n++) {
        FACTORIAL[n] = n*FACTORIAL[n-1];
    }
/*    
    SBINOMIAL = malloc((N+1)*(N+1)*sizeof(int)); 
    for (int n=0; n<=N; n++) {
        for (int k=0; k<=n; k++) {
            SBINOMIAL[n*(N+1)+k] = (k&1 ? -1 : 1 )*binomial(n, k);
        }
        for (int k=n+1; k<=N; k++) {
            SBINOMIAL[n*(N+1)+k] = 0;
        }
    }
*/    
}

static void free_factorial(void) {
    free(FACTORIAL);
//    free(SBINOMIAL);
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

int phi(INTEGER y[], int m, generator_t w[], expr_t* ex, INTEGER v[]) {
    if (m==0) {
        return 0;
    }
    switch (ex->type) {
        case IDENTITY: 
            for (int j=0; j<m; j++) {
                y[j] = v[j];
            }
            return m;
        case GENERATOR: {
            int m1=0;
            for (int j=0; j<m-1; j++) {
                if (w[j]==ex->num) {
                    y[j] = v[j+1];
                    if (y[j]!=0) {
                        m1 = j+1;
                    }
                }
                else {
                    y[j] = 0;
                }
            }
            return m1;
            }
        case SUM: { 
            INTEGER y2[m];
            int m1 = phi(y, m, w, ex->arg1, v);
            int m2 = phi(y2, m, w, ex->arg2, v);
            if (m1<m2) {
                for (int j=0; j<m1; j++) {
                    y[j] += y2[j];
                }
                for (int j=m1; j<m2; j++) {
                    y[j] = y2[j];
                }
                return m2;
            }
            else {
                for (int j=0; j<m2; j++) {
                    y[j] += y2[j];
                }
                return m1;
            }
            } 
        case DIFFERENCE: {
            INTEGER y2[m];
            int m1 = phi(y, m, w, ex->arg1, v);
            int m2 = phi(y2, m, w, ex->arg2, v);
            if (m1<m2) {
                for (int j=0; j<m1; j++) {
                    y[j] -= y2[j];
                }
                for (int j=m1; j<m2; j++) {
                    y[j] = -y2[j];
                }
                return m2;
            }
            else {
                for (int j=0; j<m2; j++) {
                    y[j] -= y2[j];
                }
                return m1;
            }
            } 
        case PRODUCT: {
            int m1 = phi(y, m, w, ex->arg2, v);
            if (m1==0) {
                return 0;
            }
            return phi(y, m1, w, ex->arg1, y);
            }
        case NEGATION: { 
            int m1 = phi(y, m, w, ex->arg1, v);
            for (int j=0; j<m1; j++) {
                y[j] = -y[j];
            }
            return m1;
            }
        case TERM: { 
            int m1 = phi(y, m, w, ex->arg1, v);
            int p = ex->num;
            int q = ex->den;
            for (int j=0; j<m1; j++) {
                INTEGER h = y[j]*p;
                INTEGER d = h/q;
                check_for_divisibility_by_int(h, q, d);
                y[j] = d;
            }
            return m1;
            }
        case EXPONENTIAL: {
            INTEGER z[m];
            for (int j=0; j<m; j++) {
                z[j] = v[j];
                y[j] = v[j];
            }
            int m1 = m;
            for (int k=1; k<m; k++) {
                m1 = phi(z, m1, w, ex->arg1, z);
                if (m1==0) {
                    return m;
                }
                if (k<=20) {
                    long int f = FACTORIAL[k]; /* fits into long int => faster execution expected */
                    for (int j=0; j<m1; j++) {
                        INTEGER d = z[j]/f;
                        check_for_divisibility_by_long_int(z[j], f, d);
                        y[j] += d;
                    }
                }
                else {
                    INTEGER f = FACTORIAL[k];
                    for (int j=0; j<m1; j++) {
                        INTEGER d = z[j]/f;
                        check_for_divisibility_by_INTEGER(z[j], f, d);
                        y[j] += d;
                    }
                }
            }
            return m;
            }
        case LOGARITHM: {
            INTEGER z[m];
            for (int j=0; j<m; j++) {
                z[j] = v[j];
                y[j] = v[j];                    
            } 
            INTEGER h[m];
            int m1 = m; 
            for (int k=1; k<m; k++) {
                for (int j=0; j<m1; j++) {
                    h[j] = z[j];
                }
                int m2 = phi(z, m1, w, ex->arg1, z);
                int m3 = 0;
                for (int j=0; j<m2; j++) {
                    z[j] -= h[j];
                    if (z[j]!=0) {
                        m3 = j+1;
                    }
                }
                for (int j=m2; j<m1; j++) {
                    z[j] = -h[j];
                    if (z[j]!=0) {
                        m3 = j+1;
                    }
                }
                if (m3==0) {
                    return m;
                }
                m1 = m3;
                int f = (k%2 ? +1 : -1)*k; /* f = (-1)^(k+1)*k */ 
                for (int j=0; j<m1; j++) {
                    INTEGER d = z[j]/f;
                    check_for_divisibility_by_int(z[j], f, d);
                    y[j] += d;
                }
            }
            return m;
            }
        default:
            fprintf(stderr, "ERROR: unknown expr type %i\n", ex->type);
            exit(EXIT_FAILURE);
    }
}

static void gen_ith_word_of_length_n(size_t i, size_t n, generator_t w[]) {
    /* METHOD: compute base K expansion of i */
    for (int j=0; j<n; j++) {
        w[j] = 0;
    }
    size_t k=n-1;
    if (K==2) {
        while (i>0) {
            w[k] = i & 1;
            i >>= 1;
            k--;
        }
    }
    else {
        while (i>0) {
            w[k] = i%K;
            i/=K;
            k--;
        }
    }
}

static void init_lookup_table() {
/* Define T, T_P such that T[i]=T0[d]+T_P2[i]*T_D1[d] where d is multi degree index of 
 * the word with index i * and T_P=T_P1.
 * Here:
 * T_D1[i] = number of Lyndon words (Lyndon basis elements) which have multi degree index i. 
 * T D2[i] = number of all words of length <= M which have multi degree index i. 
 * T_P1[i] such that Lyndon word W[i] is the T_P1[i]-th Lyndon word having multi degree 
 *         index DI[i]. 
 * T_P2[i] such that word with index i is the T_P2[i]-th word in the list of all words 
 *          having the same multi degree index as the given word with index i 
 * Then: word with index i and multi-degree index d has coefficient
 *      T[i][T_P[j]] = T0[d][[T_P1[j] + T_P2[i]*T_D1[d]]
 * in basis element with number j. 
 * Basis element j and word i are assumed to have the same multi-degree  and length <= M. 
 * Note: transposing rows and columns such that the coefficient is given by 
 * T0[d][[T_P1[j]*T_D2[d] + T_P2[i]] results in a  significant loss of performance. 
 */
    if (M==0) {
        return;
    }    
    
    double t0 = tic();
    size_t H = DI[ii[M]-1]+1; 
    uint32_t *T_D1 = calloc(H, sizeof(uint32_t));
    uint32_t *T_P1 = calloc(ii[M], sizeof(uint32_t));
    for (int i=0; i<ii[M]; i++) {
        T_P1[i] = T_D1[DI[i]];
        T_D1[DI[i]]++;
    }
    uint32_t *T_D2 = calloc(H, sizeof(uint32_t));
    uint32_t *T_P2 = calloc((ipow(K, M+1)-1)/(K-1)-1, sizeof(uint32_t));
    uint32_t *FWD = calloc(H, sizeof(uint32_t)); 
    uint32_t *WDI = calloc((ipow(K, M+1)-1)/(K-1)-1, sizeof(uint32_t));
    generator_t w[M];
    for (int n=1; n<=M; n++) {
        int os = (ipow(K, n)-1)/(K-1)-1;  
        for (int i=0; i<ipow(K, n); i++) {
            gen_ith_word_of_length_n(i, n, w);
            size_t wi = word_index(K, w, 0, n-1);
            size_t di = multi_degree_index(K, w, 0, n-1);
            if (di<H) { /* this holds for all di except the last one */
               T_P2[wi] = T_D2[di];
               T_D2[di]++;
               WDI[wi] = di; 
               if (FWD[di]==0) {
                    FWD[di] = wi - os;
               }
            }
        }
    }
    TINT_t **T0 = calloc(H, sizeof(TINT_t*));
    for (int h=0; h<H; h++) {
        size_t d = T_D1[h]*T_D2[h];
        if (d>0) {
            T0[h] = calloc(d, sizeof(TINT_t)); // !!! TODO: eventually free this memory
        }
    }

    T = calloc((ipow(K, M+1)-1)/(K-1)-1, sizeof(int*));
    for (int wi=0; wi<(ipow(K, M+1)-1)/(K-1)-1; wi++) {
        int di = WDI[wi]; 
        T[wi] = T0[di] + T_P2[wi]*T_D1[di];
    }
    
    /* case n=1: */
    for (int j=0; j<K; j++) {
        uint32_t di =  DI[j];
        T0[di][T_P1[j] + T_P2[j]*T_D1[di]] = 1;
    }

    /* n>=2: */
    for (int n=2; n<=M; n++) {
        size_t ii1 = ii[n-1];
        size_t ii2 = ii[n]-1;
        int os = (ipow(K, n)-1)/(K-1)-1;
        #pragma omp parallel for schedule(dynamic,256)
        for (int j=ii1; j<=ii2; j++) {
            uint32_t j1 = p1[j];
            uint32_t j2 = p2[j];
            uint8_t n1 = nn[j1];
            uint8_t n2 = nn[j2];
            int Kn1 = ipow(K, n1);
            int Kn2 = ipow(K, n2);
            int os1 = (Kn1-1)/(K-1)-1;
            int os2 = (Kn2-1)/(K-1)-1;
            uint32_t di = DI[j];
            uint32_t di1 = DI[j1];
            uint32_t di2 = DI[j2];
            int y1 = T_D2[di1];
            int y2 = T_D2[di2];
            int x = T_D1[di];
            int x1 = T_D1[di1];
            int x2 = T_D1[di2];
            TINT_t *L = T0[di]+T_P1[j];
            TINT_t *L1 = T0[di1]+T_P1[j1];
            TINT_t *L2 = T0[di2]+T_P1[j2];
            for (int i1=FWD[di1]; i1<=WI[j1]; i1++) {
                if (WDI[i1+os1]==di1) {
                    int i = T_P2[i1*Kn2+FWD[di2]+os];
                    int c1 = L1[T_P2[i1+os1]*x1];
                    if (c1!=0) {
                        int k = i*x;
                        int k2 = 0;
                        for (int i2=0; i2<y2; i2++) {
                            int c2 = L2[k2];
                            L[k] = c1*c2;  
                            k += x;
                            k2 += x2;
                            i++;
                        }
                    }
                }
            }
            for (int i2=FWD[di2]; i2<=WI[j2]; i2++) {
                if (WDI[i2+os2]==di2) {
                    int i = T_P2[i2*Kn1+FWD[di1]+os];
                    int c2 = L2[T_P2[i2+os2]*x2];
                    if (c2!=0) {
                        int k = i*x;
                        int k1 = 0;
                        for (int i1=0; i1<y1; i1++) {
                            int c1 = L1[k1];
                            L[k] -= c1*c2;  
                            k += x;
                            k1 += x1;
                            i++;
                        }
                    }
                }
            }
        }
    }
    T_P = T_P1;
    free(T_P2);
    free(T_D1);
    free(T_D2);
    free(FWD);
    free(WDI);
    free(T0);

    if (VERBOSITY_LEVEL>=1) {
        double t1 = toc(t0);
        printf("#lookup table for word lengths<=%li\n", M);
        printf("#init lookup table: time=%g sec\n", t1);
        if (VERBOSITY_LEVEL>=2) {
            fflush(stdout);
        }
    }
}

static void free_lookup_table(void) {
    free(T);
    free(T_P);
    // TODO: free memory as indicated above !!!
}



static int coeff_word_in_basis_element(/* generator_t w[], */ size_t l, size_t r, size_t j, size_t N1, size_t D[], TINT_t **TWI) {  
    /* computes the coefficient of the word with index wi=W2I[l+r*N] in the basis element
     * with number j.
     * W2I is a table of indices such that W2I[l'+r'*N] is the index of the subword w[l':r'] 
     * of a word w which is given only implicitely.
     * D is a table of multi degree indices such that D[l'+r'*N] is the multi degree index
     * of w[l':r']. 
     */
    int n=r-l+1;

    if (n==1) {
        return DI[j]==D[l + r*N1];
    }

    if (n<=M) {  /* use lookup table */
        return TWI[l + r*N1][T_P[j]]; 
    }
/*
    if (K==2) {
        //if (DI[j] == DI[ii[n]-1]) { // does w[l:r] and W[j] contain exactly one A ?
        if (DI[j] == DIABBB[n]) { // does w[l:r] and W[j] contain exactly one A ?
            int x=0;
            for(; (x<n) && (w[l+x]!=0); x++) {} 
            // x ... position of the unique A in w
            return SBINOMIAL[(r-l)*(N+1)+x];
        }
    }
*/

    size_t j1 = p1[j];
    size_t j2 = p2[j];
    size_t m1 = nn[j1];
    size_t m2 = r-l+1-m1;

    int mi = DI[j1];
    int c2 = 0;
    if (D[l+m2 + r*N1] == mi) {
        c2 = coeff_word_in_basis_element(/* w, */ l+m2, r, j1, N1, D, TWI); 
        if (c2!=0) {
            c2 *= coeff_word_in_basis_element(/* w, */ l, l+m2-1, j2, N1, D, TWI); 
        }
    }

    int c1 = 0;
    if (D[l + (l+m1-1)*N1] == mi) {
        c1 = coeff_word_in_basis_element(/* w, */ l+m1, r, j2, N1, D, TWI); 
        if (c1!=0) {
            c1 *= coeff_word_in_basis_element(/* w, */ l, l+m1-1, j1, N1, D, TWI); 
        }
    }

    return c1 - c2;
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
    if (VERBOSITY_LEVEL>=1) {
        printf("#expression="); print_expr(ex); printf("\n"); 
        printf("#denominator="); print_INTEGER(denom); printf("\n");
        printf("#divisibility checks are "
#ifdef NO_DIVISIBILITY_CHECKS    
            "off"
#else
            "on"
#endif
        "\n");
        if (VERBOSITY_LEVEL>=2) {
            fflush(stdout);
        }
    }
    double t0 = tic();

    INTEGER e[N+1];

    /* c[0] needs special handling */
    INTEGER t1[2];
    e[0] = 0;
    e[1] = denom;
    int  m = phi(t1, 2, W[0], ex, e);
    c[0] = m>0 ? t1[0] : 0;

    /* now the other coeffs */
    for (int j=0; j<N; j++){
        e[j] = 0;
    }
    e[N] = denom;

    size_t i1 = ii[N-1];
    size_t i2 = ii[N]-1;

    size_t h1 = DI[i1];
    size_t h2 = DI[i2];

#ifndef MERGE_WORDS_PASS
    #pragma omp parallel 
    {
    
    size_t JW[N];
    INTEGER t[N+1];

    #pragma omp for schedule(dynamic,256) 
    for (int i=i1; i<=i2; i++) {
             if (shortcut_for_classical_bch && !(N%2) && p1[i]!=0) {
                c[i] = 0;
                continue;
            }
            generator_t *w = W[i];
            int m = phi(t, N+1, w, ex, e);
            size_t kW = get_right_factors(i, JW, N);
            for (int k=0; k<=kW; k++) {
                c[JW[k]] = k<m ? t[k] : 0;
            }
    }
    }
    if (VERBOSITY_LEVEL>=1) {
        double t1 = toc(t0);
        printf("#compute coeffs of words: time=%g sec\n", t1);
        if (VERBOSITY_LEVEL>=2) {
            fflush(stdout);
        }
    }
    t0 = tic();
#endif  

    if (VERBOSITY_LEVEL>=2) {
#ifdef _OPENMP
        printf("# degree     #basis        time thread\n");
#else
        printf("# degree     #basis        time\n");
#endif
    }

    double h_time[h2-h1+1];
    int h_n[h2-h1+1];
#ifdef _OPENMP
    int h_thread[h2-h1+1];
#endif
    int hh[h2-h1+1];
    if (K==2 && (N&1)==0) {
        /* generate loop order corresponding to decreasing running times:
         * N/2, N/2-1, N/2+1, N/2-1, N/2+1, ..., 1, N-1
         */ 
        int n1 = N>>1;
        hh[0]=n1-1;
        for (int k=1; k<n1; k++) {
            hh[N-2*k-1] = k-1;
            hh[2*k+1-1] = n1+k-1;
        }
    }
    else {
        for (int k=0; k<=h2-h1; k++) {
            hh[k] = k;
        }
    }

#ifdef _OPENMP
    omp_set_nested(INNER_THREADS>1);
#endif

    #pragma omp parallel num_threads(OUTER_THREADS)
    {
    int *jj = calloc(N_LYNDON, sizeof(int));  // N_LYNDON far too large upper bound
#ifdef _OPENMP
    int *d = NULL;
    if (INNER_THREADS>1) {
        d = calloc(N_LYNDON, sizeof(int));
    }
#endif
    size_t D[N*N];
    TINT_t *TWI[N*N];
    
    size_t JW[N];
    size_t JB[N];
#ifdef MERGE_WORDS_PASS
    INTEGER t[N+1];
#endif
    /* Note: We choose schedule(dynamic, 1) because each
     * iteration of the loop is associated with a specific 
     * multi degree index, and the work to be done varies widely
     * for different multi degree indices. 
     */
    #pragma omp for schedule(dynamic,1) 
    for (int k=0; k<=h2-h1; k++) {
        int h = h1+hh[k];
        h_time[k] = tic();
        h_n[k] = 0;
#ifdef _OPENMP
        h_thread[k] = omp_get_thread_num();
#endif
        size_t kW1 = N+1; 

        int jj_max = 0; 
        for (int i=i1; i<=i2; i++) {
            if (DI[i]==h) {
                jj[jj_max] = i;
                jj_max++;
            }
        }

        for (int x=0; x<jj_max; x++) {
            int i = jj[x];
            {
                h_n[k]++;
                if (shortcut_for_classical_bch && !(N%2) && p1[i]!=0) {
                    c[i] = 0;
                    continue;
                }

                size_t kW = get_right_factors(i, JW, N);
                generator_t *w = W[i];
#ifdef MERGE_WORDS_PASS
                int m = phi(t, N+1, w, ex, e);
                for (int k=0; k<=kW; k++) {
                    c[JW[k]] = k<m ? t[k] : 0;
                }
#endif
                kW1 = kW<kW1 ? kW : kW1;
                size_t N1 = N-kW1;

                gen_D(K, N1, w+kW1, D);
                gen_TWI(K, N1, M, w+kW1, TWI);

#ifdef _OPENMP
                if (INNER_THREADS>1) {
                #pragma omp parallel for schedule(static, 512) num_threads(INNER_THREADS)
                for (int y=x-1; y>=0; y--) {
                //#pragma omp parallel for schedule(static, 1) num_threads(INNER_THREADS)
                //for (int p=0; p<INNER_THREADS; p++) {
                //for (int y=x-1-p; y>=0; y-=INNER_THREADS) {
                    int j = jj[y];
                    d[y] = 0;
                    size_t kB = get_right_factors(j, JB, N);
                    if (D[kB-kW1 + (N1-1)*N1] == DI[JB[kB]]) { // check if multi degrees match
                        d[y] = coeff_word_in_basis_element(/* w+kW1, */ kB-kW1, N1-1, JB[kB], N1, D, TWI); 
                    }
                //}
                }

                for (int y=0; y<=x-1; y++) {
                    int j = jj[y];
                    if (d[y]!=0) {
                        size_t kB = get_right_factors(j, JB, N);
                            for (int k=0; k<=kB && k<=kW; k++) {
                                c[JW[k]] -= d[y]*c[JB[k]];
                            }
                    }
                }
                }
                else {
#endif
                for (int y=0; y<=x-1; y++) {
                    int j = jj[y];
                    size_t kB = get_right_factors(j, JB, N);
                    if (D[kB-kW1 + (N1-1)*N1] == DI[JB[kB]]) { // check if multi degrees match
                        int d = coeff_word_in_basis_element(/* w+kW1, */ kB-kW1, N1-1, JB[kB], N1, D, TWI);
                        if (d!=0) {
                            for (int k=0; k<=kB && k<=kW; k++) {
                                c[JW[k]] -= d*c[JB[k]];
                            }
                        }
                    }
                }
#ifdef _OPENMP
                }
#endif
            }
        }
        h_time[k] = toc(h_time[k]); 
        if (VERBOSITY_LEVEL>=2) {
#ifdef _OPENMP
            printf("#%7i %10i %11.2f   %4i\n", hh[k]+1, h_n[k], h_time[k], h_thread[k]);
#else
            printf("#%7i %10i %11.2f\n", hh[k]+1, h_n[k], h_time[k]);
#endif
            fflush(stdout);
        }
    }
    free(jj);
#ifdef _OPENMP
    free(d);
#endif
    }

    if (VERBOSITY_LEVEL>=1) {
        double t1 = toc(t0);
        printf("#convert to lie series: time=%g sec\n", t1);
        if (VERBOSITY_LEVEL>=2) {
            fflush(stdout);
        }
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
    M = max_lookup_length;
    init_factorial();
    init_lyndon_words();
    init_lookup_table();
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
    LS.n_lyndon = N_LYNDON;
    LS.p1 = p1;
    LS.p2 = p2;
    LS.denom = denom;
    LS.c = c;
    return LS;
}

lie_series_t lie_series(size_t K, expr_t* expr, size_t N, int64_t fac, size_t M) {
    double t0 = tic();
    init_all(K, N, M);
    INTEGER *c = malloc(N_LYNDON*sizeof(INTEGER));
    INTEGER denom = FACTORIAL[N]*den_fac[N]*fac;
    compute_lie_series(expr, c, denom, 0);
    lie_series_t LS = gen_result(c, denom);
    free_all();
    if (VERBOSITY_LEVEL>=1) {
        double t1 = toc(t0);
        printf("#total time=%g sec\n", t1);
        if (VERBOSITY_LEVEL>=2) {
            fflush(stdout);
        }
    }
    return LS;
}

lie_series_t BCH(size_t N, size_t M) {
    double t0 = tic();
    expr_t *A = generator(0);
    expr_t *B = generator(1);
    expr_t *expr = logarithm(product(exponential(A), exponential(B)));
    init_all(2, N, M);
    INTEGER *c = malloc(N_LYNDON*sizeof(INTEGER));
    INTEGER denom = FACTORIAL[N]*den_fac[N];
    compute_lie_series(expr, c, denom, 1);
    lie_series_t LS = gen_result(c, denom);
    free_all();
    free_expr(A);
    free_expr(B);
    free_expr(expr);
    if (VERBOSITY_LEVEL>=1) {
        double t1 = toc(t0);
        printf("#total time=%g sec\n", t1);
        if (VERBOSITY_LEVEL>=2) {
            fflush(stdout);
        }
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
    INTEGER *c = malloc(N_LYNDON*sizeof(INTEGER));
    INTEGER denom = FACTORIAL[N]*den_fac[N];
    if (VERBOSITY_LEVEL>=1) {
        printf("#NOTE: in the following expression, A stands for A/2\n");
        if (VERBOSITY_LEVEL>=2) {
        }
    }
    compute_lie_series(expr, c, denom, 0);
    lie_series_t LS = gen_result(c, denom);
    for (int i=0; i<N_LYNDON; i++) {
        int nA = get_degree_of_generator(&LS, i, 0);
        LS.c[i] <<= N-1-nA; /* c[i] = c[i]*2^(N-1-nA) */
    }
    LS.denom <<= N-1; /* denom = denom*2^(N-1) */
    if (VERBOSITY_LEVEL>=1) {
        printf("#denominator changed to "); print_INTEGER(LS.denom); printf("\n");
        if (VERBOSITY_LEVEL>=2) {
            fflush(stdout);
        }
    }
    free_all();
    free_expr(halfA);
    free_expr(B);
    free_expr(expr);
    if (VERBOSITY_LEVEL>=1) {
        double t1 = toc(t0);
        printf("#total time=%g sec\n", t1);
        if (VERBOSITY_LEVEL>=2) {
            fflush(stdout);
        }
    }
    return LS;
}


void free_lie_series(lie_series_t LS) {
    free(LS.p1);
    free(LS.p2);
    free(LS.c);
}


void set_verbosity_level(unsigned int level) {
    VERBOSITY_LEVEL = level;
}

#ifdef _OPENMP
void set_inner_threads(unsigned int n) {
    INNER_THREADS = n;
}

void set_outer_threads(unsigned int n) {
    OUTER_THREADS = n;
}
#endif


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
    if (VERBOSITY_LEVEL>=1) {
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
        if (what & PRINT_FACTORS) printf("\t%i\t%i", LS->p1[i], LS->p2[i]);
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



