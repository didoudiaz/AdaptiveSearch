/*
 *  Adaptive search
 *
 *  Copyright (C) 2002-2014 Daniel Diaz, Philippe Codognet and Salvador Abreu
 *
 *  langford.c: Langford problem and Skolem sequences (pairs and triplets)
 *
 *  Modified Nov 2013 by Daniel Diaz (incremental error computation)
 *  Modified Mai 2014 by Daniel Diaz (extended to triplets and to Skolem sequences)
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#include "ad_solver.h"

/* define LANGFORD (default) or SKOLEM depending on the problem to solve */
#if !defined(LANGFORD) && !defined(SKOLEM)
#define LANGFORD
#endif

/* define K = 2 (default) or 3 depending on you want pairs or triplets */

#ifndef K
#define K 2
#endif



/*-----------*
 * Constants *
 *-----------*/

/*-------*
 * Types *
 *-------*/

/*------------------*
 * Global variables *
 *------------------*/

static int size;		/* copy of p_ad->size */
static int *sol;		/* copy of p_ad->sol */

static int order;		/* size / K */

static int *err;                /* errors on each value (0..order-1) */


#ifdef LANGFORD
#define DIST_OK(x)  ((x) + 2)
#else  /* SKOLEM */
#define DIST_OK(x)  ((x) + 1)
#endif




/*------------*
 * Prototypes *
 *------------*/

/*
 *  LANGFORD problem: 
 * 
 *  The problem is to arrange the 2 sets {1,2,..,n} into a single sequence in which:
 *    - between the two 1’s there is 1 number,
 *    - between the two 2’s there are 2 numbers, ...
 *    - between the two n’s there are n numbers.
 *
 *  Ex: (n=3)       2 3 1 2 1 3
 *
 *  The problem generalizes to the L(K,n) problem, which is to arrange k sets of numbers 1 to n, 
 *  so that each appearance of the number m is m numbers on from the last. 
 *
 *  Ex: (K=3, n=9)  1 8 1 9 1 5 2 6 7  2 8 5 2 9 6 4 7 5  3 8 4 6 3 9 7 4 3
 *
 *  SKOLEM sequence: 
 *
 *  This problem came from the study of the the "triple systems of Steiner". It has been formulated
 *  by Skolem as "Is it possible to distribute the number 1,2,...,2n in n pairs(a_r, b_r) s.t. we have
 *  b_r - a_r = r for r in 1..n ?".  
 *  E.g.: for n=4, the partition into pairs {(7,8),(2,4),(3,6),(1,5)} is a Skolem sequence. It may be
 *  represented as the sequence 4 2 3 2 4 3 1 1, where r occurs at positions a_r and b_r. 
 *  This problem is similar to Langford problem, except that pairs are k position apart, 
 *  i.e. between 2 consecutive values m there are m-1 numbers. 
 *  This variant was also rediscovered later by R. S. Nickerson in 1967
 *  (A variant of Langford's Problem, American Math. Monthly, 1967, 74, 591-595). 
 *
 *  Ex: (n=3)       1 1 4 2 3 2 4 3 
 *
 *  Ex: (k=3, n=9)  7 5 3 6 9 3 5 7 3 6 8 5 4 9 7 6 4 2 8 2 4 2 9 1 1 1 8 
 *
 *  For more information see John Miller's page (Skolem sequences correspond to V(K,n)): 
 *
 *  http://legacy.lclark.edu/~miller/langford.html
 *
 *  http://www.cut-the-knot.org/Curriculum/Algebra/LangfordSequence.shtml
 *
 *  http://www.m-hikari.com/imf/imf-2014/1-4-2014/shalabyIMF1-4-2014.pdf
 *
 *  Langford problem is prob024 in CSPLib (http://www.csplib.org/Problems/prob024/)
 *
 *  Here is a little Prolog program to convert a solution as a list of indexes
 *
 *  l(K, N, LP) :-                  % display a solution as a list of indexes
 *    p(K, N, LV),
 *    NK is N * K,
 *    length(LV, NK),
 *    length(LP, NK),
 *    set(LV, K, N, 0, LP),
 *    (   member(Z, LP), format(' %d', [Z]), fail ; nl). %display to be passed to the C program as input
 *  
 *  
 *  set([], _, _, _,  _).
 *  
 *  set([V|LV], K, N, I, LP) :-
 *          between(1, K, O), R is (O - 1) * N + V, nth1(R, LP, I), !, % find first hole
 *          I1 is (I + 1),
 *          set(LV, K, N, I1, LP).
 *  
 *  
 *  % Enter the solutions here as p(K, N, [values in 1..N])
 *  
 *  p(2,  8, [3,1,8,1,3,7,5,2,6,4,2,8,5,7,4,6]).
 *  
 *  p(3, 17, [14, 4,15, 6, 3, 8, 4,16, 3,17, 6, 4, 3, 7, 8,14, 9,
 *             6,15,13,11, 7,12, 8,16, 5, 9,17,10, 7,14, 5,11,13,
 *            15,12, 9, 5, 1,10, 1,16, 1, 2,11,17, 2,13,12, 2,10]).
 *  
 *  p(4, 24, [ 8,17, 1, 3, 1,16, 1, 3, 1, 8,10, 3,23,21,19, 3,11,24, 8,17, 2,10,16, 2,
 *            20,22, 2, 8,11, 2,13,18,10,15,19,21,23,17,12,16,11, 5,24,10,13,20,14, 5,
 *            22,15,18,12,11, 5,19,17,16,21,13, 5,23,14, 7, 9,12,15,20,24, 6,18, 7,22,
 *            13, 9,19, 6,14,12, 7,21, 4,15, 6, 9,23, 4, 7,20,18, 6, 4,14,24, 9,22, 4]).
 */

/*
 *  MODELING
 *
 *  order = n of the problem
 *  size  = order * K (we solve L(K, order) for K = 2 or 3)
 *  sol[] = values: sol[i] = j (j in 0..size-1) encodes one position of a given value v:
 *
 *          value v = i % order + 1
 *
 *          if i < order   the 1st occurrence of v appears in position j
 *          if i < 2*order the 2nd occurrence of v appears in position j
 *                    else the 3rd occurrence of v appears in position j
 *
 *  A solution for L(2,3) is:
 *
 *      i  : 0 1 2  3 4 5
 *      v  : 1 2 3  1 2 3
 *  sol[i] : 2 0 5  4 3 1 which represents the following sequence
 *  sequen.: 2 3 1  2 1 3
 *
 *  A solution for L(3,9) is:
 *
 *      i  :  0  1  2  3  4  5  6  7  8   9 10 11 12 13 14 15 16 17   18 19 20 21 22 23 24 25 26
 *      v  :  1  2  3  4  5  6  7  8  9   1  2  3  4  5  6  7  8  9    1  2  3  4  5  6  7  8  9
 *  sol[i] :  2 12 26 15 11  7 24 10 23   0  6 18 25  5 21 16 19 13    4  9 22 20 17 14  8  1  3
 *  sequen.:  1  8  1  9  1  5  2  6  7   2  8  5  2  9  6  4  7  5    3  8  4  6  3  9  7  4  3
 *
 *
 *  In the rest of the code we use x = v - 1 (x in 0..order-1).
 *  The error on a value x is stored in err[x].
 *  err[x] = 1 iff the distance between both occurrences of x is invalid
 *  (i.e. the distance between indices are != x + 2 for Langford and x + 1 for Skolem)
 *
 *  Remark: (Langford) the value v = order has intial an domain which is restricted.
 *          The postition of the first occurence cannot appear [order-2 .. order]
 *          For instance for n = 9, the first position of 9 cannot be 7,8,9
 *          Thus the second position (which is thus 9+1 further) cannot appear at 17,18,19
 *  This property is not used in the current modeling.
 */


/*
 *  SOLVE
 *
 *  Initializations needed for the resolution.
 */

void
Solve(AdData *p_ad)
{
  sol = p_ad->sol;
  size = p_ad->size;

  order = p_ad->size / K;

  if (err == NULL)
    {
      err = (int *) malloc(order * sizeof(int));
      if (err == NULL)
        {
          fprintf(stderr, "%s:%d malloc failed\n", __FILE__, __LINE__);
          exit(1);
        }
    }

  Ad_Solve(p_ad);
}



#define ORDER3(a, b, c) do { ind1 = sol[a]; ind2 = sol[b]; ind3 = sol[c]; } while(0)

#define NORMALIZE3(x, ind1, ind2, ind3)			\
  int i1 = x;						\
  int i2 = i1 + order;					\
  int i3 = i2 + order;					\
							\
  if (sol[i1] < sol[i2])				\
    {							\
      if (sol[i3] < sol[i1])				\
	ORDER3(i3, i1, i2);				\
      else if (sol[i3] < sol[i2])			\
	ORDER3(i1, i3, i2);				\
      else						\
	ORDER3(i1, i2, i3);				\
    }							\
  else							\
    {							\
      if (sol[i3] < sol[i2])				\
	ORDER3(i3, i2, i1);				\
      else if (sol[i3] < sol[i1])			\
	ORDER3(i2, i3, i1);				\
      else						\
	ORDER3(i2, i1, i3);				\
    }


/*
 *  COMPUTE_ERROR
 *
 *  Returns the error associated to the value x (x in 0..order-1)
 */

static int
Compute_Error(int x)		/* here x < order */
{

#if K == 2

  int ind1 = sol[x];		/* index of the 1st occurrence */
  int ind2 = sol[x + order];	/* index of the 2nd occurrence */

  return (abs(ind1 - ind2) != DIST_OK(x));

#else

#define ERR2(a, b)  if (b - a != DIST_OK(x)) r++;

  int r = 0;
  int ind1, ind2, ind3;
  NORMALIZE3(x, ind1, ind2, ind3);

  ERR2(ind1, ind2);
  ERR2(ind2, ind3);

  return r;
#endif
}




/*
 *  COST_OF_SOLUTION
 *
 *  Returns the total cost of the current solution.
 *  Also computes errors on constraints for subsequent calls to
 *  Cost_On_Variable, Cost_If_Swap and Executed_Swap.
 */

int
Cost_Of_Solution(int should_be_recorded)
{
  int x;
  int e, r = 0;

  for(x = 0; x < order; x++)
    {
      e = Compute_Error(x);
      if (should_be_recorded)
	err[x] = e;
      r += e;
    }

  return r;
}




/*
 *  COST_ON_VARIABLE
 *
 *  Evaluates the error on a variable.
 */

int
Cost_On_Variable(int i)
{
  int x = i % order;
#if K == 2
  return err[x];		/* return 0 or 1 */
#else
  return err[x] != 0; /* for K == 3 return if the variable is in error (i.e. 1 or 2 errors are the same) */
#endif
}

//#define SLOW // SLOW is not exact with the +1 for false plateau (see below) - else remove the +1

#ifndef SLOW 

/*
 *  COST_IF_SWAP
 *
 *  Evaluates the new total cost for a swap.
 */

int
Cost_If_Swap(int current_cost, int i1, int i2)
{
  int x = i1 % order;		/* value to exchange (in 0..order - 1) */
  int y = i2 % order;
  int tmp;

//#define CHECK

#ifdef CHECK
  int c;
  if (current_cost != Cost_Of_Solution(0))
    printf("ERROR1 %d <=> %d: %d should be %d\n", i1, i2, current_cost, Cost_Of_Solution(0));
#endif

#if K == 2
  if (x == y)			/* exchange the same value ? */
    return current_cost;	/* for K == 2 stay on a plateau (even if false) avoid all resets */
#else
  if (x == y)			/* exchange the same value ? */
    return current_cost + 1;	/* for K == 3 don't return current_cost to avoid "false" plateau */
#endif

  tmp = sol[i1];
  sol[i1] = sol[i2];
  sol[i2] = tmp;


  current_cost -= err[x];
  current_cost -= err[y];

  current_cost += Compute_Error(x);
  current_cost += Compute_Error(y);

#ifdef CHECK
  c = Cost_Of_Solution(0);
  if (current_cost != c)
    {
      printf("ERROR2 %d <=> %d: %d should be %d\n", i1, i2, current_cost, c);
      current_cost = c;
    }
#endif

  sol[i2] = sol[i1];
  sol[i1] = tmp;

#ifdef CHECK
  //  Cost_Of_Solution(0);
#endif

  return current_cost;
}

#endif




/*
 *  EXECUTED_SWAP
 *
 *  Records a swap.
 */

void
Executed_Swap(int i1, int i2)
{
#ifndef SLOW
  int x = i1 % order;
  int y = i2 % order;

  err[x] = Compute_Error(x);
  err[y] = Compute_Error(y);
#else
  Cost_Of_Solution(1);
#endif
}




int param_needed = 1;		/* overwrite var of main.c */

/*
 *  INIT_PARAMETERS
 *
 *  Initialization function.
 */

void
Init_Parameters(AdData *p_ad)
{
  int order = p_ad->param;

  p_ad->size = order * K;

  p_ad->first_best = 1;

#ifdef LANGFORD
  if ((K == 2 && order % 4 != 0 && order % 4 != 3) ||
      (K == 3 && (order < 9 || (order % 9 != 0 && order % 9 != 1 && order % 9 != 8))))
#else  /* SKOLEM */
  if ((K == 2 && order % 4 != 0 && order % 4 != 1) ||
      (K == 3 && ((order > 1 && order < 9) || order % 9 > 2)))
#endif
    {
      printf("no solution for size = %d\n", order);
      exit(1);
    }
  /* defaults */
  if (p_ad->prob_select_loc_min == -1)
    p_ad->prob_select_loc_min = (K == 2) ? 3 : 6;

  if (p_ad->freeze_loc_min == -1)
    p_ad->freeze_loc_min = (K == 2) ? 1 : 2;

  if (p_ad->freeze_swap == -1)
    p_ad->freeze_swap = 0;

  if (p_ad->reset_limit == -1)/* for K == 2 no reset occurs generally except of little values */
    p_ad->reset_limit = (K == 2) ? ((order < 12) ? 4 : 10) : 2;

  if (p_ad->reset_percent == -1)
    p_ad->reset_percent = 1;

  if (p_ad->restart_limit == -1) /* K == 2 pefer to stop when no chance (for little values) */
    p_ad->restart_limit = (K == 2) ? 500000 : ((1U << 31) - 1);

  if (p_ad->restart_max == -1)	/* and restart some times */
    p_ad->restart_max = 1000;
}



/*
 *  DISPLAY_SOLUTION
 *
 *  Displays a solution.
 */
void
Display_Solution(AdData *p_ad)
{
  int i, j;
  int order = p_ad->size / K;

  Ad_Display(p_ad->sol, p_ad, NULL); // to see actual values
  for(i = 0; i < p_ad->size; i++)
    {
      for(j = 0; p_ad->sol[j] != i; j++)
	;
      j %= order;
      printf("%2d ", j + 1);
    }
  printf("\n");
}


/*
 *  CHECK_SOLUTION
 *
 *  Checks if the solution is valid.
 */

int
Check_Solution(AdData *p_ad)
{
  int order = p_ad->size / K;
  int *sol = p_ad->sol;
  int between, x;

  int i = Random_Permut_Check(p_ad->sol, p_ad->size, p_ad->actual_value, p_ad->base_value);

  if (i >= 0)
    {
      printf("ERROR: not a valid permutation, error at [%d] = %d\n", i, p_ad->sol[i]);
      return 0;
    }

#define CHK(a, b)								\
  between = abs(a - b);								\
  if (between != DIST_OK(x))							\
    {										\
      printf("ERROR: between two %d there are %d values !\n", i + 1, between); 	\
      return 0;									\
    }


  for(x = 0; x < order; x++)
    {
#if K == 2
      int ind1 = sol[x];
      int ind2 = sol[x + order];
      CHK(ind1, ind2);
#else
      int ind1, ind2, ind3;
      NORMALIZE3(x, ind1, ind2, ind3);
      CHK(ind1, ind2);
      CHK(ind2, ind3);
#endif
    }

  return 1;
}
