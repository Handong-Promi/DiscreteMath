#include <stdio.h>
#include <string.h>
#include "intset.h"

int main(){
    
    typedef enum { false, true } bool;

    FILE * fp = fopen("formula", "w") ;

    int s ; // size of the gird (s x s)
    int i, j; // i: rows, j: colomns.

    // 1. Get the size.
    printf("\n");
    scanf("%d", &s);

    // 2. Declare the propositional values.
     for (i = 1 ; i <= s ; i++)
		for (j = 1 ; j <= s ; j++)
			fprintf(fp,"(declare-const p%d%d Bool)\n", i, j); // Truth value: thee cell(i,j) has mine

    // 3. Make the formula <Formular Constructor>

    // Q1. Get the standard input for Minesweeper  (Checking the pre-assigned cells)
    char input;
    int num; 
    
    int r, c; // for surrounding cells...

    printf("\n----- Input -----\n");
    fprintf(fp,"; Q1\n");
	fprintf(fp,"(assert (and ");
    for(i = 1 ; i <= s ; i++){ 
        for(j = 1 ; j <= s ; j++){
            scanf(" %c", &input);
            num = input - '0';
            if(num >= 0 && num <= 8){
                fprintf(fp, "(and (not p%d%d) (or ", i, j);
                intset * s = intset_alloc() ;
                for(r = i-1 ; r <= i+1 ; r++){
                    for(c = j-1 ; c <= j+1 ; c++){
                        if(r<1||c<1) continue;
                        if(r>10||c>10) continue;
                        if(r==i && c==j) continue;
                        if(r==10 && c!=10)
                            intset_add(s, r*10+c);
                        else if(r!=10&&c==10)
                            intset_add(s, r*100+c);
                        else if(r==10&&c==10)
                            intset_add(s, r*100+c);
                        else
                            intset_add(s, r*10+c);
                    }
                }

                if(num==0){
                    fprintf(fp, "(not (or ");
                    for(int i = 0 ; i < s->n_elems ; i++){
                         fprintf(fp, "p%d ", s->elems[i]) ;
                    }
                    fprintf(fp,"))");
                }
                else{
                    size_t n_ps ;
                    intset ** ps = intset_subsets(s, num, &n_ps) ;

                    for(int i = 0 ; i < n_ps ; i++){
                        fprintf(fp, "(and ");
                        for (int j = 0 ; j < ps[i]->n_elems ; j++) {
                            fprintf(fp, "p%d ", ps[i]->elems[j]) ;
                        }
                        fprintf(fp, ")");
                    }
                }
                fprintf(fp, ")) ");
            }   
        }
    }
    fprintf(fp, "))\n");
    printf("-----------------\n");

    fclose(fp) ;

    FILE * fin = popen("z3 formula", "r") ;
    char check[128];
	char buf[128] ;
	fscanf(fin, "%s %s", check, buf) ;
    printf("%s\n", check);
	while (!feof(fin)) {
        
		fscanf(fin, "%s", buf) ; printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; printf("%s ", buf) ;
		fscanf(fin, "%s", buf) ; printf("%s\n", buf) ;
	}
	pclose(fin) ;

    /*
    FILE * fin = popen("z3 formula", "r") ;
    char checkSat[128] ;
	char buf[128] ;
	fscanf(fin, "%s %s", checkSat, buf) ;

    bool isSat; // to check whether z3 returns sat or unsat, if it's unsat, print "there... problem!" and jump to end. else, keep going.
    if(strcmp(checkSat, "unsat") == 0){
        isSat = false;
        printf("\nThere is no solution for given problem!\n\n");
    }
    else{
        isSat = true;
        FILE * res = fopen("result", "w") ;

        char checkProTrue[128];
        char propo[128];

        while (!feof(fin)) {

            fscanf(fin, "%s", buf) ; // (define-fun
            fscanf(fin, "%s", propo) ; // proposition variable
            fscanf(fin, "%s", buf) ; // ()
            fscanf(fin, "%s", buf) ; // Bool
            fscanf(fin, "%s", checkProTrue) ; // true or false

            checkProTrue[strlen(checkProTrue)-1] = '\0'; // because the raw is "ture)" or "false)"

            if(strcmp(checkProTrue, "true")==0) fprintf(res, "%s\n", propo) ;
        }
        fclose(res) ;
        pclose(fin) ;
	}
    */
}