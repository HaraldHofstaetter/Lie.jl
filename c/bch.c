#include<stdlib.h>
#include<stdio.h>
#include<assert.h>
#include<time.h>


static unsigned char **W;
static unsigned int *p1;
static unsigned int *p2;
static unsigned int *nn;
static unsigned int *ii;
static unsigned int n_lyndon;



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


void gen_lyndon_words(unsigned int K, unsigned int N) {
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


enum expr_type { UNDEFINED, GENERATOR, SUM, PRODUCT, COMMUTATOR, TERM, 
                 EXPONENTIAL, LOGARITHM };

typedef struct expr {
    enum expr_type type;
    struct expr *arg1;
    struct expr *arg2;
    int num;
    int den;
} expr;

expr* undefined_expr(void) {
    expr *g = malloc(sizeof(expr));
    g->type = UNDEFINED;
    g->arg1 = NULL;
    g->arg2 = NULL;
    g->num = 0;
    g->den = 0;
    return g;
}

expr* generator(unsigned char n) {
    expr *g = undefined_expr();
    g->type = GENERATOR;
    g->num = n;
    return g;
}

expr* sum(expr* arg1, expr* arg2) {
    expr *g = undefined_expr();
    g->type = SUM;
    g->arg1 = arg1;
    g->arg2 = arg2;
    return g;
}

expr* product(expr* arg1, expr* arg2) {
    expr *g = undefined_expr();
    g->type = PRODUCT;
    g->arg1 = arg1;
    g->arg2 = arg2;
    return g;
}

expr* commutator(expr* arg1, expr* arg2) {
    expr *g = undefined_expr();
    g->type = COMMUTATOR;
    g->arg1 = arg1;
    g->arg2 = arg2;
    return g;
}

expr* term(int num, int den, expr* arg) {
    expr *g = undefined_expr();
    g->type = TERM;
    g->arg1 = arg;
    g->num = num;
    g->den = den;
    return g;
}

expr* exponential(expr* arg) {
    expr *g = undefined_expr();
    g->type = EXPONENTIAL;
    g->arg1 = arg;
    return g;
}

expr* logarithm(expr* arg) {
    expr *g = undefined_expr();
    g->type = LOGARITHM;
    g->arg1 = arg;
    return g;
}



int main(void) {
    const unsigned N=20;
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
    clock_t t0 = clock();
    gen_lyndon_words(K, N);
    clock_t t = clock()-t0;
    printf("time for generating Lyndon words: t=%g\n", t /((double) CLOCKS_PER_SEC));
/*    
    for (int i=0; i<=N; i++) {
        printf("ii[%i] = %i\n", i, ii[i]);
    }
  
    for (int i=0; i<ii[N]; i++) {
        printf("%8i %5i %8i %8i  ", i, nn[i], p1[i], p2[i]);
        print_word(nn[i], W[i]);
        printf("\n");
    }
 */
    expr *A = generator(0);
    expr *B = generator(1);
    expr *BCH = logarithm(sum(exponential(A), exponential(B)));

    return EXIT_SUCCESS ;
}
