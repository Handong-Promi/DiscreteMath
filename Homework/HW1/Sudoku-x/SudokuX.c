#include <stdio.h>
#include <string.h>

int main(){
    
    typedef enum { false, true } bool;

    FILE * fp = fopen("formula", "w") ;

    int i, j, n, m, r, s; // i: rows, j: columns, n, m: the number of a certain cell, r, s: variables for grids

    // 1. Declare the propositional values.
    for (i = 1 ; i <= 9 ; i++)
		for (j = 1 ; j <= 9 ; j++)
            for(n = 1 ; n <= 9 ; n++)
			    fprintf(fp,"(declare-const p%d%d%d Bool)\n", i, j, n);


    // 2. Make the formula <Formular Constructor>

    // Q1. Get the standard input for Sudoku-X  (Checking the pre-assigned cells)
    char input;
    int value; 
    
    printf("\n----- Input -----\n");
    fprintf(fp,"; Q1\n");
	fprintf(fp,"(assert (and ");
    for(i = 1 ; i <= 9 ; i++){ 
        for(j = 1 ; j <= 9 ; j++){
            scanf(" %c", &input);
            value = input - '0';
            if(value >= 1 && value <= 9){
                fprintf(fp, "p%d%d%d ", i, j, value);
            }   
        }
    }
    fprintf(fp, "))\n");
    printf("-----------------\n");
                 
    //Q2. Constraint for cells: Each cell is assigned with exactly one number
    
    //Q2-1 : at most once
    fprintf(fp,"; Q2-1\n");
    fprintf(fp,"(assert (and ");
    for(i = 1 ; i <= 9 ; i++){
        fprintf(fp, "(and ");
        for(j = 1 ; j <= 9 ; j++){
            fprintf(fp, "(and ");
            for(n = 1 ; n <= 8 ; n++){
                fprintf(fp, "(and ");
                for(m = n+1 ; m <= 9 ; m++){
                    fprintf(fp, "(not (and p%d%d%d p%d%d%d))", i, j, n, i, j, m);
                }
                fprintf(fp, ")");
            }
            fprintf(fp, ")");
        }
        fprintf(fp, ")");
    }
    fprintf(fp, "))\n");

    //Q2-2. at least once.
    fprintf(fp,"; Q2-2\n");
    fprintf(fp,"(assert (and ");
    for(i=1;i<=9;i++){
        fprintf(fp, "(and ");
        for(j=1;j<=9;j++){
            fprintf(fp, "(or ");
            for(n=1;n<=9;n++){
                fprintf(fp, "p%d%d%d ", i, j, n);
            }
            fprintf(fp, ")");
        }
        fprintf(fp, ")");
    }
    fprintf(fp, "))\n");


    //Q3. Constraint for rows: Every row has all 9 numbers.
    fprintf(fp, "; Q3\n");
    fprintf(fp, "(assert (and ");
    for(i=1;i<=9;i++){
        fprintf(fp, "(and ");
        for(n=1;n<=9;n++){
            fprintf(fp, "(or ");
            for(j=1;j<=9;j++){
                fprintf(fp, "p%d%d%d ", i, j, n);
            }
            fprintf(fp, ")");
        }
        fprintf(fp, ")");
    }
    fprintf(fp, "))\n");

    //Q4. Constraint for columns: Every column has all 9 numbers.
    fprintf(fp, "; Q4\n");
    fprintf(fp, "(assert (and ");
    for(j=1;j<=9;j++){
        fprintf(fp, "(and ");
        for(n=1;n<=9;n++){
            fprintf(fp, "(or ");
            for(i=1;i<=9;i++){
                fprintf(fp, "p%d%d%d ", i, j, n);
            }
            fprintf(fp, ")");
        }
        fprintf(fp, ")");
    }
    fprintf(fp, "))\n");

    //Q5. Constraint for subgirds: Every subgird has all 9 numbers.
    fprintf(fp, "; Q5\n");
    fprintf(fp, "(assert (and ");
    for(r=0;r<=2;r++){
        fprintf(fp, "(and ");
        for(s=0;s<=2;s++){
            fprintf(fp, "(and ");
            for(n=1;n<=9;n++){
                fprintf(fp, "(or ");
                for(i=1;i<=3;i++){
                    fprintf(fp, "(or ");
                    for(j=1;j<=3;j++){
                        fprintf(fp, "p%d%d%d ", 3*r+i, 3*s+j, n);
                    }
                    fprintf(fp, ")");
                }
                fprintf(fp, ")");
            }
            fprintf(fp, ")");
        }
        fprintf(fp, ")");
    }
    fprintf(fp, "))\n");

    //Q6. Constraint for diagonals: each of the two diagonals has all 9 numbers. 
    
    //Q6-1. from left top to right bottm
    fprintf(fp, "; Q6-1\n");
    fprintf(fp, "(assert (and ");
    for(n=1;n<=9;n++){
        fprintf(fp, "(or ");
        for(i=1, j=1; i<=9&&j<=9; i++,j++){
            fprintf(fp, "p%d%d%d ", i, j, n);
        }
        fprintf(fp, ")");
    }
    fprintf(fp, "))\n");
    
    
    //Q6-2. from right top to left bottom
    fprintf(fp, "; Q6-2\n");
    fprintf(fp, "(assert (and ");
    for(n=1;n<=9;n++){
        fprintf(fp, "(or ");
        for(i=1, j=9; i<=9&&j>=1; i++,j--){
            fprintf(fp, "p%d%d%d ", i, j, n);
        }
        fprintf(fp, ")");
    }
    fprintf(fp, "))\n");
    
    fprintf(fp,"(check-sat)\n(get-model)\n") ;

	fclose(fp) ;


    // 3. Pass this formula to z3 and save the solution of assignments to a certain file, in order to pass the that file to Z3 output interpreter

	FILE * fin = popen("z3 formula", "r") ;
    char checkSat[128] ;
	char buf[128] ;
	fscanf(fin, "%s %s", checkSat, buf) ;

    bool isSat; // to check whether z3 returns sat or unsat, if it's unsat, print "there... problem!" and jump to end. else, keep going.
    if(strcmp(checkSat, "unsat") == 0){
        isSat=false;
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

    // 4. print the final output of solved puzzle unless the value isSat is false;
    if(isSat){

        int SudokuX[9][9];
        char validPropo[128];

        FILE * res = fopen("result", "r") ;

        int i,j;
        while(!feof(res)){
            fscanf(res, "%s", validPropo);
            i = validPropo[1] - '0' - 1 ; // Because i, j in SudokuX[9][9] start from index 0. 
            j = validPropo[2] - '0' - 1 ;
            SudokuX[i][j] = validPropo[3] - '0';
        }
        fclose(res);

        printf("\n----- Output ----\n");
        for(i=0;i<9;i++){
            for(j=0;j<9;j++){
                printf("%d ", SudokuX[i][j]);
            }
            printf("\n");
        }        
        printf("-----------------\n\n");          

    }

    return 0;
}