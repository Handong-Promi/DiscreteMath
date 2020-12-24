#include <stdio.h>
#include <stdlib.h>
#include "graph.h"

typedef enum _boolean{
	FALSE,
	TRUE
} boolean;

const int INF = 10000000; // because the range of weight is from 1 to 100,000, I just set 1,000,000 as infinite number for this program.

void initDistance(int start, int* d, graph_t* g){
	// For readability, I followed i / j / k as the sequence of index identifier of multi-demsion array 
	for(int j = 0; j < g->n_vertices; j++) {
		if(j == start) d[j] = 0;
		else{
			if(g->m[start][j] == 0) d[j] = INF;
			else{
				int min = INF;
				for(int k = 0 ; k < g->m[start][j] ; k++){
					if(g->w[start][j][k] < min)
						min = g->w[start][j][k];
				}
				d[j] = min;
			}
		}
	}
}

int getClosest(boolean* v, int* d, int n_vertices) {
	int min = INF;
	int index = 0;
	for(int i = 0; i < n_vertices; i++) {
		if(d[i] < min && !v[i]) {
			min = d[i];
			index = i;
		}
	}
	return index;
} 

int* dijkstra(int start, int end, graph_t* g) {

	// visited node -> "is it visited?"
	boolean *v = (boolean*) calloc(g->n_vertices, sizeof(int)); 
	// shortest length of the path from starting node to ending node -> "weight"
	int *d = (int*) calloc(g->n_vertices, sizeof(int));
	
	initDistance(start, d, g);

	v[start] = TRUE;

	for(int i = 0; i < g->n_vertices - 2; i++) {
		if(v[end] == TRUE) break;
		int current = getClosest(v, d, g->n_vertices);
		//printf("i: %d, current: %d\n", i, current);
		v[current] = TRUE;
		for(int j = 0; j < g->n_vertices; j++) {
			if(!v[j]) {

				if(g->m[current][j] == 0) continue;
				else{
					int min = INF;
					for(int k = 0 ; k < g->m[current][j] ; k++){
						if(g->w[current][j][k] < min)
							min = g->w[current][j][k];
					}
					if(d[current] + min < d[j]) {
						d[j] = d[current] + min;
					}
				}
			}
		}
		/*
		printf("\n");
		for(int i = 0 ; i < g->n_vertices; i ++)
			printf("d[%d]: %d\n", i, d[i]);
		printf("\n");
		*/
	}
	free(v);
	

	/*
	char s1[10];
	sprintf(s1, "%d", d[end]);
	printf("d[end] -> d[%d]: %s\n", end, d[end]==INF ? "INF" : s1);
	*/

	if(d[end] == INF) return 0x0;
	else return d;
}

int
main (int argc, char ** args)
{
	graph_t * g ; 

	g = graph_read_stdin() ;

	if (argc != 3) { 
		fprintf(stderr, "Too few arguments\n") ;
		return 1 ;
	}

	int start, end ;

	start = atoi(args[1]) ;
	end = atoi(args[2]) ;

	if (start < 0 || g->n_vertices <= start ||
		end < 0 || g->n_vertices <= end) {
		fprintf(stderr, "Wrong arguments\n") ;
		return 1 ;
	}

	int*  result = dijkstra(start, end, g);
	
	if(result!=0x0) printf("%d\n", result[end]);
	
	free(result);
	graph_free(g) ;
	return 0 ;
}
