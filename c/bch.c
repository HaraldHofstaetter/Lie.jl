#include<stdlib.h>
#include<stdio.h>
#include<assert.h>
#include<time.h>

/* typedef  __int128_t INTEGER; */
typedef  __int64_t INTEGER;


static unsigned char **W;
static unsigned int *p1;
static unsigned int *p2;
static unsigned int *nn;
static unsigned int *ii;
static unsigned int n_lyndon;
static INTEGER *FACTORIAL;



void moebius_mu(unsigned int N, int mu[N]) {
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

void number_of_lyndon_words(unsigned int K, unsigned int N, int nLW[N]) {
    /* INPUT: K ... number of letters
     *        N ... maximum lenght of lyndon words
     * OUTPUT: nLW[n] ... number of lyndon words with K letters of length n+1, n=0,...,N-1
     * METHOD: Witt's formula
     */
    int powK[N+1];
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
            d += 1;
        }
        if (d*d == n) {
            h += mu[d-1]*powK[d];
        }
        nLW[n-1] = h/n;
    }
}

void print_word(unsigned int n, unsigned char w[]) {        
    for (int j=0; j<n; j++) {
           printf("%i", w[j]);
    }
}

int compare_words(unsigned int n1, unsigned char w1[],
                  unsigned int n2, unsigned char w2[]) {
    if (n1<n2) {
        return -1;
    }
    else if (n1>n2) {
        return +1;
    }
    for (int j=0; j<n1; j++) {
        if (w1[j]<w2[j]) {
            return -1;
        }
        else if (w1[j]>w2[j]) {
            return +1;
        }
    }
    return 0;
}

unsigned int find_lyndon_word(unsigned int l, unsigned int r, unsigned int n, unsigned char w[]) {
    while (l<=r) {
        unsigned int m = l + (r-l)/2;
        int s = compare_words(nn[m], W[m], n, w);
        if (s==0) {
            return m;
        }
        if (s<0) {
            l = m+1;
        }
        else {
            r = m-1;
        }
    }
    printf("NOT FOUND: ");
    print_word(n, w);
    printf("\n");
    assert(0); /* should not reach this point, otherwise word not found */ 
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

void genLW(unsigned int K, unsigned int n, unsigned int t, unsigned int p[], 
           unsigned char a[], size_t *wp, unsigned int split[]) {
    if (t>n) {
        if (p[0]==n) {
            for (int i=0; i<n; i++) {
                W[*wp][i] = a[i+1];
            }
            if (n>1) {
                unsigned int m = split[(n-1)*n]; /* split[1,n] */
                p1[*wp] = find_lyndon_word(0, *wp-1, m-1, W[*wp]);
                p2[*wp] = find_lyndon_word(0, *wp-1, n-m+1, W[*wp]+m-1);
            }
            (*wp)++;
        }
    }
    else {
        unsigned int q[n];
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


void init_lyndon_words(unsigned int K, unsigned int N) {
    int nLW[N];
    number_of_lyndon_words(K, N, nLW);
    size_t mem_len = 0;
    n_lyndon = 0; /* global variable */
    for (int n=1; n<=N; n++) {
        n_lyndon += nLW[n-1];
        mem_len += n*nLW[n-1];
    }
    W = malloc(n_lyndon*sizeof(unsigned char *)); /*TODO check for error */
    p1 = malloc(n_lyndon*sizeof(unsigned int)); /*TODO check for error */
    p2 = malloc(n_lyndon*sizeof(unsigned int)); /*TODO check for error */
    nn = malloc(n_lyndon*sizeof(unsigned int)); /*TODO check for error */
    ii = malloc((N+1)*sizeof(unsigned int)); /*TODO check for error */
    W[0] = malloc(mem_len*sizeof(unsigned char)); /*TODO check for error */ 
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

    unsigned char a[N+1];
    unsigned int p[N];
    unsigned int split[N*N];
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
}

void init_factorial(unsigned int N) {
    FACTORIAL = malloc((N+1)*sizeof(INTEGER)); /*TODO check for error */
    FACTORIAL[0] = 1;
    for (int n=1; n<=N; n++) {
        FACTORIAL[n] = n*FACTORIAL[n-1];
    }
}

void init_all(unsigned int K, unsigned int N) {
    init_factorial(N);
    init_lyndon_words(K, N);
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

expr* generator(unsigned char n) {
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
            printf("unknown expr type %i\n", ex->type);
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


void phi(INTEGER y[], int n, unsigned char w[], expr* ex, INTEGER v[]) {
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
            INTEGER z[n+1];
            phi(y, n, w, ex->arg1, v);
            phi(z, n, w, ex->arg2, v);
            for (int j=0; j<=n; j++) {
                y[j] += z[j];
            }
            } 
            break;
        case DIFFERENCE: {
            INTEGER z[n+1];
            phi(y, n, w, ex->arg1, v);
            phi(z, n, w, ex->arg2, v);
            for (int j=0; j<=n; j++) {
                y[j] -= z[j];
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
                    printf("dividend not divisble by %i\n", q);
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
                           printf("dividend not divisble by %li\n", f);
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
                           printf("dividend not divisble by %li\n", f);
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
                       printf("dividend not divisble by %i\n", f);
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
            printf("unknown expr type %i\n", ex->type);
            assert(0);
    }
}




int main(void) {
    const unsigned N=5;
    const unsigned K=2;
/*
    int mu[N];
    moebius_mu(N, mu);
    for (int i=0; i<N; i++) {
        printf("mu(%i) = %i\n", i+1, mu[i]);
    }

    
    int nLW[N];
    number_of_lyndon_words(K, N, nLW);
    for (int i=0; i<N; i++) {
        printf("number of lyndon words of length %i = %i\n", i+1, nLW[i]);
    }
*/
    clock_t t = clock();
    init_all(K, N);
    t = clock()-t;
    printf("time for generating Lyndon words: t=%g\n", t /((double) CLOCKS_PER_SEC));
/*    
    for (int i=0; i<=N; i++) {
        printf("ii[%i] = %i\n", i, ii[i]);
    }
  
 */
    expr *A = generator(0);
    expr *B = generator(1);
    expr *BCH = logarithm(product(exponential(A), exponential(B)));
    //expr *BCH = difference(product(exponential(A), exponential(B)),identity());
    // expr *BCH = difference(product(A,product(B,product(product(A, B),B))), product(A,sum(A,B)));
    //
    
    printf("S=");
    print_expr(BCH);
    printf("\n");

    INTEGER denom = FACTORIAL[N]*2*3;
    //INTEGER denom = 1;

    INTEGER *c = malloc(n_lyndon*sizeof(INTEGER));
    INTEGER y[N+1];
    INTEGER e[N+1];

    t = clock();
    for (int n=0; n<n_lyndon; n++) {
        for (int j=0; j<=nn[n]; j++) {
            e[j] = 0;
        }
        e[nn[n]] = denom;
        phi(y, nn[n], W[n], BCH, e);
        c[n] = y[0]; 
    }
    t = clock()-t;
    printf("time for coeffs of Lyndon words: t=%g\n", t /((double) CLOCKS_PER_SEC));

    for (int n=0; n<n_lyndon; n++) {
        printf("%8i    ", n);
        print_word(nn[n], W[n]);
        printf(" %8li/%li\n", c[n], denom);
    }


    return EXIT_SUCCESS ;
}
