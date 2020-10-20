#include <stdio.h>
#include <string.h>
#include <stdlib.h>

int converToInt(char input);

int main(){

    typedef enum { false, true } bool;

    FILE * fp = fopen("formula", "w") ;

    int s; // size of the grid. (S x S)
    int i, j; // i: rows, j: columns.
    int k; // just a loop varialbe.
    char l, n, m; // a: letter, n, m: the letter of a certain cell

    printf("\n--- Input --\n");

    // 1. Get the size.
    scanf("%d", &s);

    // 2. Declare the propositional values.
    for (i = 1 ; i <= s ; i++)
		for (j = 1 ; j <= s ; j++)
            for(l= 'A' ; l <= 'E' ; l++)
                fprintf(fp, "(declare-const p%d%d%c Bool)\n", i, j, l);

    // 3. Make the formula <Formular Constructor>

    // Q1. [Detail] constraint: check annotations and save them into formula.

    char input;
    

    fprintf(fp, "; Q1\n");
    fprintf(fp, "(assert (and ");
    for(int ri = 1 ; ri <= 4 ; ri++){ // ri: row for input. // total ri is 4 (top, bottom. left, right).
        // fprintf(fp, "(and "); // not sure whether this conjunction should exist - what if there are no annotation? it is empty compound proposition, then does z3 work?
        for(int ci = 1 ; ci <= s ; ci++){ // ci: column for input.
            scanf(" %c", &input);
            if(input >= 'A' && input <='E'){

                switch(ri){
                    case 1: 
                        j = ci;
                        fprintf(fp, "(or ");
                        for(i=1;i<=s-4;i++){ // s-4: size - length of left letters (4). 
                            fprintf(fp, "(and ");
                            fprintf(fp, "p%d%d%c ", i, j, input);
                            for(k=1;k<i;k++){
                                fprintf(fp, "(not (or ");
                                for(l='A'; l<='E'; l++){
                                        fprintf(fp, "p%d%d%c ", k, j, l);
                                }
                                fprintf(fp, "))");
                            }
                            fprintf(fp, ") ");
                        }
                        fprintf(fp, ") "); break;
                    case 2:
                        j = ci;
                        fprintf(fp, "(or "); 
                        for(i=s;i>4;i--){ // the reason i's minimum is 5 is there should be at least 4 spaces for left 4 letters.
                            fprintf(fp, "(and ");
                            fprintf(fp, "p%d%d%c ", i, j, input);
                            for(k=s;k>i;k--){
                                fprintf(fp, "(not (or ");
                                for(l='A'; l<='E'; l++){
                                        fprintf(fp, "p%d%d%c ", k, j, l);
                                }
                                fprintf(fp, "))");
                            }
                            fprintf(fp, ") ");
                        }
                        fprintf(fp, ") "); break;
                    case 3:
                        i = ci;
                        fprintf(fp, "(or "); 
                        for(j=1;j<=s-4;j++){ // s-4: size - length of left letters (4). 
                            fprintf(fp, "(and ");
                            fprintf(fp, "p%d%d%c ", i, j, input);
                            for(k=1;k<j;k++){
                                fprintf(fp, "(not (or ");
                                for(l='A'; l<='E'; l++){
                                        fprintf(fp, "p%d%d%c ", i, k, l);
                                }
                                fprintf(fp, "))");
                            }
                            fprintf(fp, ") ");
                        }
                        fprintf(fp, ") "); break;
                    case 4:
                        i = ci;
                        fprintf(fp, "(or "); 
                        for(j=s;j>4;j--){ // s-4: size - length of left letters (4). 
                            fprintf(fp, "(and ");
                            fprintf(fp, "p%d%d%c ", i, j, input);
                            for(k=s;k>j;k--){
                                fprintf(fp, "(not (or ");
                                for(l='A'; l<='E'; l++){
                                        fprintf(fp, "p%d%d%c ", i, k, l);
                                }
                                fprintf(fp, "))");
                            }
                            fprintf(fp, ") ");
                        }
                        fprintf(fp, ") "); break;
                }
            }

        }
    }
    fprintf(fp, "))\n");
    printf("------------\n");

    // [General]

    //Q2. Constraint for cells: the non-empty cell is assigned with exactly one number
    // This means, the every none-empty cell is assigned at most one letter.
    fprintf(fp, "; Q2\n");
    fprintf(fp, "(assert (and ");
    for(i=1; i<=s; i++){
        fprintf(fp, "(and ");
        for(j=1;j<=s;j++){
            fprintf(fp, "(and ");
            for(n = 'A'; n <= 'D'; n++){
                fprintf(fp, "(and ");
                for(m = n+1; m <= 'E'; m++){
                    fprintf(fp, "(not (and p%d%d%c p%d%d%c))", i, j, n, i, j, m);
                }
                fprintf(fp, ")");
            }
            fprintf(fp, ")");
        }
        fprintf(fp, ")");
    }
    fprintf(fp, "))\n");

    //Q3. Constraint for rows: Every row has all 5 letters.
    fprintf(fp, "; Q3\n");
    fprintf(fp, "(assert (and ");
    for(i=1;i<=s;i++){
        fprintf(fp, "(and ");
        for(l='A';l<='E';l++){
            fprintf(fp, "(or ");
            for(j=1;j<=s;j++){
                fprintf(fp, "p%d%d%c ", i, j, l);
            }
            fprintf(fp, ")");
        }
        fprintf(fp, ")");
    }
    fprintf(fp, "))\n");

    //Q4. Constraint for rows: Each letter may appear only once on the row.
    fprintf(fp,"; Q4\n") ;
	fprintf(fp,"(assert (and ") ;
	for (i = 1 ; i <= s ; i++) {
		fprintf(fp,"(and ") ;
        for(l = 'A'; l<='E'; l++){
            fprintf(fp, "(and ");
            for (j = 1 ; j <= s-1 ; j++) {
			    fprintf(fp,"(and ") ;
                for (k = j + 1 ; k <= s ; k++) {
                    fprintf(fp,"(not (and p%d%d%c p%d%d%c))", i, j, l, i, k, l) ;
                }
			    fprintf(fp,")") ;
	    	}
            fprintf(fp, ")");
        }
		fprintf(fp,") ") ;
	}
	fprintf(fp,"))\n") ;

    //Q5. Constraint for columns: Every column has all 5 letters.
    fprintf(fp, "; Q5\n");
    fprintf(fp, "(assert (and ");
    for(j=1;j<=s;j++){
        fprintf(fp, "(and ");
        for(l='A';l<='E';l++){
            fprintf(fp, "(or ");
            for(i=1;i<=s;i++){
                fprintf(fp, "p%d%d%c ", i, j, l);
            }
            fprintf(fp, ")");
        }
        fprintf(fp, ")");
    }
    fprintf(fp, "))\n");

    //Q6. Constraint for columns: Each letter cmay appear only once on the column
    fprintf(fp,"; Q6\n") ;
	fprintf(fp,"(assert (and ") ;
	for (j = 1 ; j <= s ; j++) {
		fprintf(fp,"(and ") ;
        for(l = 'A'; l<='E'; l++){
            fprintf(fp, "(and ");
            for (i = 1 ; i <= s-1 ; i++) {
			    fprintf(fp,"(and ") ;
                for (k = i + 1 ; k <= s ; k++) {
                    fprintf(fp,"(not (and p%d%d%c p%d%d%c))", i, j, l, k, j, l) ;
                }
			    fprintf(fp,")") ;
	    	}
            fprintf(fp, ")");
        }
		fprintf(fp,") ") ;
	}
	fprintf(fp,"))\n") ;

    fprintf(fp,"(check-sat)\n(get-model)\n") ;

    fclose(fp) ;

    /* // For debugging formula
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
    */

    // 3. Pass this formula to z3 and save the solution of assignments to a certain file, in order to pass the that file to Z3 output interpreter
	
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
    
    
    // 4. print the final output of solved puzzle unless the value isSat is false;
    if(isSat){

        char **EasyAsABC;
        EasyAsABC = (char**) malloc ( sizeof(char*) * s );
        for(k=0; k<s; k++)
            EasyAsABC[k] = (char*) malloc ( sizeof(char) * s );

        for(i=0;i<s;i++)
            for(j=0;j<s;j++)
                EasyAsABC[i][j] = '_'; // Initialize as '_', empty.

        char validPropo[128];

        FILE * res = fopen("result", "r") ;

        int i,j;
        while(!feof(res)){
            fscanf(res, "%s", validPropo);
            if(strlen(validPropo) == 4){
                i = validPropo[1] - '0' - 1 ; // Because i, j in EasyAsABC[s][s] start from index 0. 
                j = validPropo[2] - '0' - 1 ;
                EasyAsABC[i][j] = validPropo[3];
                
            }
            else if(strlen(validPropo)==5) { // When either i or j is 1o.  
                if(validPropo[2] == '0'){ // this means the i is 10 ("p10__").
                    i = (validPropo[1] - '0') * 10 -1;
                    j = validPropo[3] - '0' - 1;
                    EasyAsABC[i][j] = validPropo[4];
                }
                else{ // This means the j is 10 ("p_10_").
                    i = validPropo[1] - '0' - 1;
                    j = (validPropo[2] - '0') * 10 -1;
                    EasyAsABC[i][j] = validPropo[4];
                }
            }
            else{ // the strlen(validProp) == 6, when both of i and j are 10. 
                i = (validPropo[1] - '0') * 10 -1;
                j = (validPropo[3] - '0') * 10 -1;
                EasyAsABC[i][j] = validPropo[5];
            }
        }
        fclose(res);

        printf("\n-- Output --\n");
        for(i=0;i<s;i++){
            for(j=0;j<s;j++){
                printf("%c ", EasyAsABC[i][j]);
            }
            printf("\n");
        }        
        printf("------------\n\n");      

        free(EasyAsABC);    

    }

    return 0;

}