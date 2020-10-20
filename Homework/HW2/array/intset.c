#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "intset.h"

intset *
intset_alloc ()
{	
	intset * s = (intset *) malloc(sizeof(intset)) ;
	s->n_elems = 0 ;
	s->elems = 0x0 ;
	return s ;
}

intset * 
intset_clone (intset * orig) 
{
	if (orig == 0x0)
		return 0x0 ;

	intset * s = intset_alloc() ;
	
	s->n_elems = orig->n_elems ;
	s->elems = 0x0 ;
	if (s->n_elems > 0) {
		s->elems = (int *) calloc(s->n_elems, sizeof(int)) ;
		memcpy(s->elems, orig->elems, s->n_elems * sizeof(int)) ;
	}
	return s ;
}

void
intset_print (FILE * fp, intset * s)
{
	fprintf(fp, "{") ;
	for (int i = 0 ; i < s->n_elems ; i++) {
		char * delim = (i > 0) ? ", " : "" ;
		fprintf(fp, "%s%d", delim, s->elems[i]) ;
	}
	fprintf(fp, "}") ;
}

void
intset_free (intset * s) 
{
	free(s->elems) ;
	free(s) ;
}

int
intset_size (intset * s) 
/*
 * returns the number of elements contained in s.
 */
{

	if(s == 0x0) return -1; // if s is invalid
	if(s->n_elems<0) return -1; // if something is wrong with s->n_elems

	
	intset * unique = intset_alloc();

	for(int i = 0 ; i < s->n_elems ; i++){
		if(intset_contains(unique, s->elems[i]) == 0)
			intset_add(unique, s->elems[i]);
	}
	
	/*
	int temp;
	int isDub;

	for(int i = 0 ; i < s->n_elems ; i++){

		isDub = 0;
		temp = s->elems[i];	

		if(i==0){
			unique->elems = (int *) malloc(sizeof(int));
			unique->elems[unique->n_elems] = temp;
			unique->n_elems++;
			continue;
		}

		for(int j = 0 ; j < unique->n_elems; j++){
			if(unique->elems[j]==temp){
				isDub=1;
				break;
			}
		}
		if(!isDub){
			unique->elems = (int *) realloc(unique->elems, sizeof(int)*((unique->n_elems)+1));
			unique->elems[unique->n_elems] = temp;
			unique->n_elems++;
		}
	}
	*/

	int size = unique->n_elems;
	
	intset_free(unique);

	return size;

}

int
intset_add (intset * s, int e) 
/*
 * insert a new integer value e to s.
 * return 0 if succeeded. return 1 if it fails.
 * 
 * hint: use realloc. note that s->elems is NULL when it has no element.
 */
{	

	if(s == 0x0) return 1; // if s is invalid
	if(s->n_elems<0) return 1; // if something is wrong with s->n_elems

	if(intset_contains(s, e)) return 1;
	/*
	int isDub = 0;

	for(int i = 0 ; i < s->n_elems ; i++){
		if(e == s->elems[i]){
			isDub = 1;
			break;	
		}
	}

	if(isDub){
		return 1;
	}
	*/

	if(s->n_elems==0){
		s->elems = (int *) malloc(sizeof(int));
		s->elems[s->n_elems] = e;
		s->n_elems++;
	}
	else{
		s->elems = (int *) realloc(s->elems, sizeof(int)*((s->n_elems)+1));
		s->elems[s->n_elems] = e;
		s->n_elems++;
	}

	return 0;

}

int
intset_remove (intset * s, int e) 
/*
 * remomve e from s.
 * return 0 if succeeded. return 1 if failed.
 *
 * s->elems must be set to NULL if s->n_elems == 0.
 *
 * hint: use realloc.
 */
{	

	if(s == 0x0) return 1; // if s is invalid
	if(s->n_elems<0) return 1; // if something is wrong with s->n_elems

	int isExist = 0;

	int i;
	for(i = 0 ; i < s->n_elems ; i++){
		if(e == s->elems[i]){
			isExist = 1;
			break;	
		}
	}

	if(!isExist){
		return 1;
	}

	for(int j = i; j < (s->n_elems)-1 ; j++){
		s->elems[j] = s->elems[j+1];
	}
	s->elems = realloc(s->elems, sizeof(int)*((s->n_elems)-1));
	s->n_elems--;

	if(s->n_elems==0){
		free(s->elems);
		s->elems = 0x0;
	}

	return 0;
}

int
intset_contains (intset * s, int e) 
/*
 * return 1 if e is contained in s. return 0 otherwise.
 */
{	

	if(s == 0x0) return 0; // if s is invalid
	if(s->n_elems<0) return 0; // if something is wrong with s->n_elems

	int isExist = 0;

	for(int i = 0 ; i < s->n_elems ; i++){
		if(s->elems[i]==e){
			isExist = 1;
			break;
		}
	}

	return isExist;

}

int
intset_equals (intset *s1, intset *s2) 
/*
 * return 1 if two sets s1 and s2 are equivalent.
 * return 0 otherwise.
 */
{	
	
	if(s1 == 0x0 || s2 == 0x0) return 0; // if at least one of sets is invalid
	if(s1->n_elems<0 || s2->n_elems<0) return 0; // if something is wrong with at least one of s->n_elems

	intset * unique1 = intset_alloc();
	intset * unique2 = intset_alloc();

	// Get the distinctive elements from s1
	for(int i = 0 ; i < s1->n_elems ; i++){
		if(intset_contains(unique1, s1->elems[i]) == 0)
			intset_add(unique1, s1->elems[i]);
	}

	// Get the distinctive elements from s2
	for(int i = 0 ; i < s2->n_elems ; i++){
		if(intset_contains(unique2, s2->elems[i]) == 0)
			intset_add(unique2, s2->elems[i]);
	}

	if(unique1->n_elems != unique2->n_elems) return 0; // the two sets are not equal to each other because the size of distinctive set of each set is different.
	
	int isEqual = 1; // assume the two sets are eaqul to each other.

	// if the two set is equal to each other, each of two distinctive set must be same. 
	// Therefore, examining whether all of unique1->elems are in the unique2->elems or not is the way to check the equality.
	for(int i = 0 ; i < unique1->n_elems ; i++){
		if(intset_contains(unique2, unique1->elems[i]) == 0){
			isEqual = 0;
			break;
		}
	}
	
	intset_free(unique1);
	intset_free(unique2);

	return isEqual;
}

intset *
intset_union (intset *s1, intset *s2) 
/*
 * return a new intset object that contains the result of
 * the union of s1 and s2.
 *
 * return NULL if the operation fails.
 */
{
	if(s1 == 0x0 || s2 == 0x0) return NULL; // if at least one of sets is invalid
	if(s1->n_elems<0 || s2->n_elems<0) return NULL; // if something is wrong with at least one of s->n_elems

	intset * unique1 = intset_alloc();
	intset * unique2 = intset_alloc();

	// Get the distinctive elements from s1
	for(int i = 0 ; i < s1->n_elems ; i++){
		if(intset_contains(unique1, s1->elems[i]) == 0)
			intset_add(unique1, s1->elems[i]);
	}

	// Get the distinctive elements from s2
	for(int i = 0 ; i < s2->n_elems ; i++){
		if(intset_contains(unique2, s2->elems[i]) == 0)
			intset_add(unique2, s2->elems[i]);
	}

	intset * Union = intset_clone(unique1);

	for(int i = 0 ; i < unique2->n_elems ; i++)
		if(intset_contains(Union, unique2->elems[i]) == 0) 
			intset_add(Union, unique2->elems[i]);
	
	intset_free(unique1);
	intset_free(unique2);

	return Union;
}

intset *
intset_intersection (intset *s1, intset *s2) 
/*
 * return a new intset object that contains the result of
 * the intersection of s1 and s2.
 *
 * return NULL if the operation fails.
 */
{
	if(s1 == 0x0 || s2 == 0x0) return NULL; // if at least one of sets is invalid
	if(s1->n_elems<0 || s2->n_elems<0) return NULL; // if something is wrong with at least one of s->n_elems

	intset * unique1 = intset_alloc();
	intset * unique2 = intset_alloc();

	// Get the distinctive elements from s1
	for(int i = 0 ; i < s1->n_elems ; i++){
		if(intset_contains(unique1, s1->elems[i]) == 0)
			intset_add(unique1, s1->elems[i]);
	}

	// Get the distinctive elements from s2
	for(int i = 0 ; i < s2->n_elems ; i++){
		if(intset_contains(unique2, s2->elems[i]) == 0)
			intset_add(unique2, s2->elems[i]);
	}

	intset * Intersection = intset_alloc();

	for(int i = 0 ; i < unique1->n_elems ; i++)
		if(intset_contains(unique2, unique1->elems[i]))
			intset_add(Intersection, unique1->elems[i]);
	
	intset_free(unique1);
	intset_free(unique2);

	return Intersection;
}

intset *
intset_difference (intset *s1, intset *s2) 
/*
 * return a new intset object that contains the result of
 * the set difference of s1 and s2 (i.e., s1 \ s2).
 *
 * return NULL if the operation fails.
 */
{
	if(s1 == 0x0 || s2 == 0x0) return NULL; // if at least one of sets is invalid
	if(s1->n_elems<0 || s2->n_elems<0) return NULL; // if something is wrong with at least one of s->n_elems

	intset * unique1 = intset_alloc();
	intset * unique2 = intset_alloc();

	// Get the distinctive elements from s1
	for(int i = 0 ; i < s1->n_elems ; i++){
		if(intset_contains(unique1, s1->elems[i]) == 0)
			intset_add(unique1, s1->elems[i]);
	}

	// Get the distinctive elements from s2
	for(int i = 0 ; i < s2->n_elems ; i++){
		if(intset_contains(unique2, s2->elems[i]) == 0)
			intset_add(unique2, s2->elems[i]);
	}

	intset * Difference = intset_alloc();

	for(int i = 0 ; i < unique1->n_elems ; i++)
		if(intset_contains(unique2, unique1->elems[i]) == 0)
			intset_add(Difference, unique1->elems[i]);
	
	intset_free(unique1);
	intset_free(unique2);

	return Difference;
}

intset **
intset_subsets (intset * s, size_t k , size_t * n_subsets) 
/*
 * return a new intset array that contains all distinct subsets
 * of s having k elements. The size of the result array must be
 * given to n_subsets.
 * 
 * this operation must be implemented with a recursion.
 *
 * return NULL if the operation fails.
 */
{
	if(s == 0x0) return NULL; // if the set is invalid
	if(s->n_elems < 0) return NULL; // if something is wrong with s->n_elems

	intset * u = intset_alloc(); // u means unique, that represents the set only having distinctive elements.

	// Get the distinctive elements from s1
	for(int i = 0 ; i < s->n_elems ; i++)
		if(intset_contains(u, s->elems[i]) == 0)
			intset_add(u, s->elems[i]);
	// finishing of getting the set only having distinctive elements.

	if(u->n_elems < k) return NULL;

	// Recursion part
	intset ** subsets;
	if(k==0){
		subsets = (intset **) malloc(sizeof(intset *));
		*n_subsets = 0;
		subsets[*n_subsets] = intset_alloc();
		*n_subsets += 1; // beacuse there is no initializing code for n_sumbsets, I should initialize this on here.
		return subsets;
	}
	else{
		int e;
		size_t count = 0; // temp of *n_subsets;
		for(int i = 0 ; i < u->n_elems ; i++){ // for every 'e'

			e = u->elems[i];
			intset * segment = intset_alloc();
			intset_add(segment, e);
			 
			intset ** subsetsPrime = intset_subsets(intset_difference(u, segment), k-1, n_subsets);
			
			for(int j = 0 ; j < *n_subsets ; j++){
				subsetsPrime[j] = intset_union(subsetsPrime[j], segment);
			}
			
			if(i == 0)
				subsets = (intset **) calloc(*n_subsets, sizeof(intset *));
			else
				subsets = (intset **) realloc(subsets, sizeof(intset *) * (count + *n_subsets));
			
			for(int j = 0 ; j < *n_subsets ; j++){
				subsets[j+count] = intset_clone(subsetsPrime[j]);
			}
			count += *n_subsets;
			free(subsetsPrime);
		}		
		
		for(int i = 0 ; i < count ; i++){
			for(int j = 0 ; j < count ; j ++){
				if(i==j) continue;
				if(intset_equals(subsets[i], subsets[j])){
					intset_free(subsets[j]);
					for(int k = j; k < count-1 ; k++){
						subsets[k] = subsets[k+1];
					}
					subsets = realloc(subsets, sizeof(int*) * (count -1));
					count -= 1;
				}
			}
		}

		*n_subsets = count;
		return subsets;	
	}

}

intset ** 
intset_powerset (intset * s, size_t * n_subsets) 
/*
 * return a new intset array that contains all distinct subsets
 * of s having. The size of the  result array must be given to
 * n_subsets.
 * 
 * this operation must be implemented with a recursion.
 *
 * return NULL if the operation fails.
*/
{
	if(s == 0x0) return NULL; // if the set is invalid
	if(s->n_elems < 0) return NULL; // if something is wrong with s->n_elems

	intset * u = intset_alloc(); // u means unique, that represents the set only having distinctive elements.

	// Get the distinctive elements from s1
	for(int i = 0 ; i < s->n_elems ; i++)
		if(intset_contains(u, s->elems[i]) == 0)
			intset_add(u, s->elems[i]);
	// finishing of getting the set only having distinctive elements.

	// Recursion part
	intset ** powerset;
	if(u->n_elems == 0){
		powerset = (intset **) malloc(sizeof(intset *));
		*n_subsets = 0;
		powerset[*n_subsets] = intset_alloc();
		*n_subsets += 1; // beacuse there is no initializing code for n_sumbsets, I should initialize this on here.
		return powerset;
	}
	else{
		int e;
		size_t count = 0; // temp of *n_subsets;
		for(int i = 0 ; i < u->n_elems ; i++){ // for every 'e'

			e = u->elems[i];
			intset * segment = intset_alloc();
			intset_add(segment, e);
			 
			intset ** subsetsPrime = intset_powerset(intset_difference(u, segment), n_subsets);

			if(i == 0)
				powerset = (intset **) calloc(*n_subsets*2, sizeof(intset *)); // *n_subsets * 2 -> becasue we should include the original subsetsPrime and the Union of subsetPrime.
			else
				powerset = (intset **) realloc(powerset, sizeof(intset *) * (count + *n_subsets * 2));

			for(int j = 0 ; j < *n_subsets; j++){ 
				powerset[j+count] = intset_clone(subsetsPrime[j]);
			}
			count += *n_subsets;

			for(int j = 0 ; j < *n_subsets; j++){
				powerset[j+count] = intset_union(subsetsPrime[j], segment);
			}
			
			count += *n_subsets;
			free(subsetsPrime);
		}	

		for(int i = 0 ; i < count ; i++){
			for(int j = 0 ; j < count ; j ++){
				if(i==j) continue;
				if(intset_equals(powerset[i], powerset[j])){
					intset_free(powerset[j]);
					for(int k = j; k < count-1 ; k++)
						powerset[k] = powerset[k+1];
		
					powerset = realloc(powerset, sizeof(int*) * (count -1));
					count -= 1;
				}
			}
		}

		*n_subsets = count;
		return powerset;
	}
}
