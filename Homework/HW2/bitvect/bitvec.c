#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "intset.h"

intset *
intset_alloc (int * univ, size_t n_univ) 
{	
	intset * s = (intset *) malloc(sizeof(intset)) ;

	s->univ = univ ;
	s->n_univ = n_univ ;

	size_t bitvect_len = n_univ / 8 + ((n_univ % 8) ? 1 : 0) ;

	s->bitvect = (unsigned char *) malloc(bitvect_len) ;
	memset(s->bitvect, 0, bitvect_len) ;
	s->n_elems = 0 ;
	return s ;
}

intset * 
intset_clone (intset * orig) 
{
	if (orig == 0x0)
		return 0x0 ;

	intset * s ;
	s = intset_alloc(orig->univ, orig->n_univ) ;
	memcpy(s->bitvect, orig->bitvect, orig->n_univ / 8 + ((orig->n_univ % 8) ? 1 : 0)) ;
	s->n_elems = orig->n_elems ;

	return s ;
}

void
intset_print (FILE * fp, intset * s)
{
	fprintf(fp, "{") ;
	char * delim = "" ;
	for (int i = 0 ; i < s->n_univ ; i++) {
		if (intset_contains(s, s->univ[i])) {
			fprintf(fp, "%s%d", delim, s->univ[i]) ;
			delim = ", " ;
		}
	}
	fprintf(fp, "}") ;
}

void
intset_free (intset * s) 
{
	free(s->bitvect) ;
	free(s) ;
}

int
intset_size (intset * s) 
/*
 * returns the number of elements contained in s.
 */
{	
	if(s == 0x0) return -1;

	return s->n_elems;

	/*
	int count = 0;
	for(int i = 0 ; i < s->n_univ ; i++){
		if(intset_contains(s, s->univ[i])) count++;
	}

	return count;
	*/
}

int
intset_add (intset * s, int e) 
/*
 * insert a new integer value e to s.
 * return 0 if succeeded. return 1 if it fails.
 * 
 */
{
	if(s == 0x0) return 1;
	int isExist = 0;
	int index;
	for(int i = 0 ; i < s->n_univ ; i++){
		if(e == s->univ[i]){
			// printf("index: %d\n", i);
			isExist = 1;
			index = i;
			break;
		}
	}
	if(!isExist) return 1; // e is not involved in univ.

	int section = index/8;
	index %= 8;
	// printf("real index: %d, section: %d\n", index, section);

	unsigned char num = 1;
	num <<= 7-index; // 1byte == 8bit, if 0000 0001 shifts left to 7, it is 1000 0000. So the 7 is the limit.
	// printf("e: %d, num: %d, s->bitvect[section] : %d\n", e, num, s->bitvect[section]);
	if((s->bitvect[section] & num) == num) return 1; // e aleardy exists in s->bitvect[section];
	s->bitvect[section] |= num;
	// printf("e: %d, num: %d, s->bitvect[section] : %d\n\n", e, num, s->bitvect[section]);
	s->n_elems++;

	return 0;
}

int
intset_remove (intset * s, int e) 
/*
 * remomve e from s.
 * return 0 if succeeded. return 1 if failed.
 *
 */
{
	if(s == 0x0) return 1;
	int isExist = 0;
	int index;
	for(int i = 0 ; i < s->n_univ ; i++){
		if(e == s->univ[i]){
			// printf("index: %d\n", i);
			isExist = 1;
			index = i;
			break;
		}
	}
	if(!isExist) return 1; // e is not involved in univ.

	int section = index/8;
	index %= 8;
	// printf("real index: %d, section: %d\n", index, section);

	unsigned char num = 1;
	num <<= 7-index; // 1byte == 8bit, if 0000 0001 shifts left to 7, it is 1000 0000. So the 7 is the limit.
	// printf("e: %d, num: %d, s->bitvect[section] : %d\n", e, num, s->bitvect[section]);
	if((s->bitvect[section] & num) != num) return 1; // e doesn't exist in s->bitvect[section];
	s->bitvect[section] ^= num;
	// printf("e: %d, num: %d, s->bitvect[section] : %d\n\n", e, num, s->bitvect[section]);
	s->n_elems--;

	return 0;
}

int
intset_contains (intset * s, int e) 
/*
 * return 1 if e is contained in s. return 0 otherwise.
 */
{
	if(s == 0x0) return 0;
	int isExist = 0;
	int index;
	for(int i = 0 ; i < s->n_univ ; i++){
		if(e == s->univ[i]){
			isExist = 1;
			index = i;
			break;
		}
	}
	if(!isExist) return 0; // e is not involved in univ.

	int section = index/8;
	index %= 8;

	unsigned char num = 1;
	num <<= 7-index;

	if((s->bitvect[section] & num) == num) return 1;
	return 0;
}	

int
intset_equals (intset *s1, intset *s2) 
/*
 * return 1 if two sets s1 and s2 are equivalent.
 * return 0 otherwise.
 *
 * two sets are not equivalent if their univ fields are not the same.
 */
{
	if(s1 == 0x0 || s2 == 0x0) return 0;
	if(s1->n_elems < 0 || s1->n_elems < 0) return 0;
	if(s1->n_univ != s2->n_univ) return 0;
	
	int isExist; // two sets are not equivalent if their univ fields are not the same.
	for(int i = 0 ; i < s1->n_univ ; i++){
		isExist = 0;
		for(int j = 0 ; j <s2->n_univ ; j++){
			if(s1->univ[i] == s2->univ[j]){
				isExist = 1; break;
			}
		}
		if(isExist == 0) return 0;
	}

	// if the two set is equal to each other, each of two distinctive set must be same. 
	// Therefore, examining whether all of s1->elems are in the s2->elems or not is the way to check the equality.

	int isEqual = 1; // assume the two sets are eaqul to each other.
	for(int i = 0 ; i < s1->n_univ ; i++){
		if(intset_contains(s1, s1->univ[i]) == 0) continue;
		if(intset_contains(s2, s1->univ[i]) == 0){
			isEqual = 0;
			break;
		}
	}
	if(isEqual==1){
		for(int i = 0 ; i < s2->n_univ ; i++){
			if(intset_contains(s2, s2->univ[i]) == 0) continue;
			if(intset_contains(s1, s2->univ[i]) == 0){
				isEqual = 0;
				break;
			}
		}
	}
	
	return isEqual;
}

intset *
intset_union (intset *s1, intset *s2) 
/*
 * return a new intset object that contains the result of
 * the union of s1 and s2.
 *
 * return NULL if the operation fails.
 * union operation fails if their univ fields are not the same.
 */
{
	if(s1 == 0x0 || s2 == 0x0) return NULL;
	if(s1->n_elems < 0 || s1->n_elems < 0) return NULL;
	if(s1->n_univ != s2->n_univ) return NULL;

	int isExist; // two sets are not equivalent if their univ fields are not the same.
	for(int i = 0 ; i < s1->n_univ ; i++){
		isExist = 0;
		for(int j = 0 ; j <s2->n_univ ; j++){
			if(s1->univ[i] == s2->univ[j]){
				isExist = 1; break;
			}
		}
		if(isExist == 0) return NULL;
	}

	intset * Union = intset_clone(s1);

	for(int i = 0 ; i < s2->n_univ ; i++){
		if(intset_contains(s2, s2->univ[i]) == 0) continue;
		intset_add(Union, s2->univ[i]); // filtering the duplicates automatically because there is a fucntion that filters duplicates, in intset_add()
	}

	return Union;

}


intset *
intset_intersection (intset *s1, intset *s2) 
/*
 * return a new intset object that contains the result of
 * the intersection of s1 and s2.
 *
 * return NULL if the operation fails.
 * intersection operation fails if their univ fields are not the same.
 */
{
	if(s1 == 0x0 || s2 == 0x0) return NULL;
	if(s1->n_elems < 0 || s1->n_elems < 0) return NULL;
	if(s1->n_univ != s2->n_univ) return NULL;

	int isExist; // two sets are not equivalent if their univ fields are not the same.
	for(int i = 0 ; i < s1->n_univ ; i++){
		isExist = 0;
		for(int j = 0 ; j <s2->n_univ ; j++){
			if(s1->univ[i] == s2->univ[j]){
				isExist = 1; break;
			}
		}
		if(isExist == 0) return NULL;
	}

	intset * Intersection = intset_alloc(s1->univ, s1->n_univ); // above codes assert that the univ and n_univ of s1 and s2 is same with each other.

	for(int i = 0 ; i < s1->n_univ ; i++){
		if(intset_contains(s1, s1->univ[i]) == 0) continue;
		if(intset_contains(s2, s1->univ[i]))
			intset_add(Intersection, s1->univ[i]); // filtering the duplicates automatically because there is a fucntion that filters duplicates, in intset_add()
	}

	return Intersection;
}


intset *
intset_difference (intset *s1, intset *s2) 
/*
 * return a new intset object that contains the result of
 * the set difference of s1 and s2 (i.e., s1 \ s2).
 *
 * return NULL if the operation fails.
 * set difference operation fails if their univ fields are not the same.
 */
{
	if(s1 == 0x0 || s2 == 0x0) return NULL;
	if(s1->n_elems < 0 || s1->n_elems < 0) return NULL;
	if(s1->n_univ != s2->n_univ) return NULL;

	int isExist; // two sets are not equivalent if their univ fields are not the same.
	for(int i = 0 ; i < s1->n_univ ; i++){
		isExist = 0;
		for(int j = 0 ; j <s2->n_univ ; j++){
			if(s1->univ[i] == s2->univ[j]){
				isExist = 1; break;
			}
		}
		if(isExist == 0) return NULL;
	}

	intset * Difference = intset_alloc(s1->univ, s1->n_univ); // above codes assert that the univ and n_univ of s1 and s2 is same with each other.

	for(int i = 0 ; i < s1->n_univ ; i++){
		if(intset_contains(s1, s1->univ[i]) == 0) continue;
		if(intset_contains(s2, s1->univ[i]) == 0)
			intset_add(Difference, s1->univ[i]); // filtering the duplicates automatically because there is a fucntion that filters duplicates, in intset_add()
	}

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
	if(s->n_elems < k) return NULL;
	
	// Recursion part
	intset ** subsets;
	if(k==0){
		subsets = (intset **) malloc(sizeof(intset *));
		*n_subsets = 0;
		subsets[*n_subsets] = intset_alloc(s->univ, s->n_univ);
		*n_subsets += 1; // beacuse there is no initializing code for n_sumbsets, I should initialize this on here.
		return subsets;
	}
	else{
		int e;
		size_t count = 0; // temp of *n_subsets;
		for(int i = 0 ; i < s->n_univ ; i++){ // for every 'e'
			if(intset_contains(s, s->univ[i]) == 0) continue;
			printf("contained info: i: %d, e: %d \n", i, s->univ[i]);
			e = s->univ[i];
			intset * segment = intset_alloc(s->univ, s->n_univ);
			intset_add(segment, e);
			printf("segement: "); intset_print(stderr, segment); fprintf(stderr, "\n") ;

			intset ** subsetsPrime = intset_subsets(intset_difference(s, segment), k-1, n_subsets);
			
			for(int j = 0 ; j < *n_subsets ; j++){
				subsetsPrime[j] = intset_union(subsetsPrime[j], segment);
			}
			
			if(i == 0)
				subsets = (intset **) calloc(*n_subsets, sizeof(intset *));
			else
				subsets = (intset **) realloc(subsets, sizeof(intset *) * (count + *n_subsets));
			
			printf("before clone: i: %d, e: %d \n", i, s->univ[i]);
			for(int j = 0 ; j < *n_subsets ; j++){
				subsets[j+count] = subsetsPrime[j];
			}
			printf("after clone: i: %d, e: %d \n", i, s->univ[i]);
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
 * of s having. The size of the result array must be given to
 * n_subsets.
 * 
 * this operation must be implemented with a recursion.
 *
 * return NULL if the operation fails.
*/
{
	if(s == 0x0) return NULL; // if the set is invalid
	if(s->n_elems < 0) return NULL; // if something is wrong with s->n_elems

	// Recursion part
	intset ** powerset;
	if(s->n_elems == 0){
		powerset = (intset **) malloc(sizeof(intset *));
		*n_subsets = 0;
		powerset[*n_subsets] = intset_alloc(s->univ, s->n_univ);
		*n_subsets += 1; // beacuse there is no initializing code for n_sumbsets, I should initialize this on here.
		return powerset;
	}
	else{
		int e;
		size_t count = 0; // temp of *n_subsets;
		for(int i = 0 ; i < s->n_univ ; i++){ // for every 'e'
			if(intset_contains(s, s->univ[i])==0) continue;
			e = s->univ[i];
			intset * segment = intset_alloc(s->univ, s->n_univ);
			intset_add(segment, e);
			 
			intset ** subsetsPrime = intset_powerset(intset_difference(s, segment), n_subsets);

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
