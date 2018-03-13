/*
 *  Adaptive search
 *
 *  Copyright (C) 2002-2013 Daniel Diaz, Philippe Codognet and Salvador Abreu
 *
 *  smti.c: Stable Matching problem with Ties and Incomplete lists
 */

/*
 * TODO: pass p1 and p2 to generate SMTI and not only pure SM problems
 * optimization: keep the best so far (modify ad_solver.c)
 * use p1 and p2 as probabilities (not integers)
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

#include "ad_solver.h"

#define SMTI_NO_MAIN
#include "smti-utils.c"

#define USE_NEXT_J

	/* Generate (when an int is given as param to main()) a new problem at each exec (-b execs) */
#define GENER_NEW_AT_EACH_EXEC


/*-----------*
 * Constants *
 *-----------*/

/*-------*
 * Types *
 *-------*/


typedef int MyShort;

/*------------------*
 * Global variables *
 *------------------*/

static int size;		/* copy of p_ad->size */
static SMPInfo smp_info;
static SMPMatrix pref_m, pref_w;
static SMPMatrix revp_m, revp_w;

static int *sol_m;		/* copy of p_ad->sol (so it is an array of int) */
static int *sol_w;
static MyShort *error;
static MyShort *bp_swap;
static int nb_bp;		/* nb of BP (for reset) */
static int nb_singles;		/* nb of singles (for reset) */
static int single_i;		/* index of single to reset */


/*------------*
 * Prototypes *
 *------------*/

/*
 *  MODELING
 */



/*
 *  SOLVE
 *
 *  Initializations needed for the resolution.
 */

void
Solve(AdData *p_ad)
{
  size = p_ad->size;

#ifdef GENER_NEW_AT_EACH_EXEC
  if (p_ad->data32[0] == 1 && pref_m != NULL)
    {
      SMP_Free_Matrix(pref_m, size);
      SMP_Free_Matrix(pref_w, size);
      SMP_Free_Matrix(revp_m, size);
      SMP_Free_Matrix(revp_w, size);
      pref_m = pref_w = NULL;
    }
#endif

  if (pref_m == NULL)		/* matrices not yet read */
    {
      if (p_ad->data32[0] == 1)
	SMP_Generate_Problem(size, 0, 0, &smp_info);
      else			/* generate a problem */
	SMP_Load_Problem(p_ad->param_file, &smp_info);
    }

  sol_m = p_ad->sol;		/* the vector is for the men */
  if (sol_w == NULL)
    {
      sol_w = malloc(size * sizeof(*sol_w));
      error = malloc(size * sizeof(*error));
      bp_swap = malloc(size * sizeof(*bp_swap));
      if (sol_w == NULL || error == NULL || bp_swap == NULL)
        {
          fprintf(stderr, "%s:%d malloc failed\n", __FILE__, __LINE__);
          exit(1);
        }
    }
  pref_m = smp_info.pref_m;
  pref_w = smp_info.pref_w;

  int m, w, k, z, rank;
  revp_m = SMP_Alloc_Matrix(size);
  revp_w = SMP_Alloc_Matrix(size);
  for(m = 0; m < size; m++)
    {
      memset(revp_m[m], -1, size * sizeof(revp_m[m][0])); /* everything set to -1 */
      for(k = 0; (z = pref_m[m][k]) >= 0; k++)
	{
	  Unpack(z, w, rank);
	  revp_m[m][w] = rank;
	}
    }
  for(w = 0; w < size; w++)
    {
      memset(revp_w[w], -1, size * sizeof(revp_w[w][0])); /* everything set to -1 */
      for(k = 0; (z = pref_w[w][k]) >= 0; k++)
	{
	  Unpack(z, m, rank);
	  revp_w[w][m] = rank;
	}
    }

  Ad_Solve(p_ad);
}




#define Find_Rank_In_Pref_M(m, w) (revp_m[m][w])
#define Find_Rank_In_Pref_W(w, m) (revp_w[w][m])





/*
 *  BLOCKING_PAIR_ERROR
 *
 *  Returns the error if (m,w) forms a BP (0 else)
 */

int
Blocking_Pair_Error(int w, int m_of_w, int m)
{
  int rank_m_of_w = Find_Rank_In_Pref_W(w, m_of_w);
  int rank_m = Find_Rank_In_Pref_W(w, m);

  int err;
  if (rank_m < 0)		/* m is not a valid partner for w - no error */
    err = 0;
  else if (rank_m_of_w < 0)	/* woman w is single */
    err = 1;			/* what else ? */
  else
    {
      err = rank_m_of_w - rank_m; /* if err > 0 (m,w) is a BP (blocking pair) */
      if (err < 0)		
	err = 0;
    }

  return err;
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
  int m, w_of_m, w, m_of_w;
  int k, z, rank_w_of_m, rank_w;
  int count_bp = 0;
  int count_singles = 0;

  for (m = 0; m < size; m++)
    {
      w_of_m = sol_m[m];
      rank_w_of_m = Find_Rank_In_Pref_M(m, w_of_m); /* -1 is m is single */

      int error_m = 0;
      int bp_swap_m = -1;		/* NB: -1 to avoid false positive in the test of Cost_If_Swap */
      
      if (rank_w_of_m < 0)	/* man m is single */
	{
	  rank_w_of_m = size;	/* check all */
	  count_singles++;
	  if (should_be_recorded && Random(count_singles) == 0)
	    single_i = m;
	}

      for(k = 0; (z = pref_m[m][k]) >= 0; k++)
	{
	  Unpack(z, w, rank_w);
	  
	  if (rank_w >= rank_w_of_m) /* stop when rank of w is >= rank of curr partner of m */
	    break;

	  m_of_w = sol_w[w];

	  error_m = Blocking_Pair_Error(w, m_of_w, m);

	  if (error_m > 0)		/* (m,w) is a BP (blocking pair) */
	    {
	      bp_swap_m = m_of_w;
	      count_bp++;	/* count the number of BP */
	      break;		/* only consider undominated BP */
	    }
	}

      if (should_be_recorded)
	{
	  error[m] = error_m;
	  bp_swap[m] = bp_swap_m;
	}
    }

  if (should_be_recorded)
    {
      nb_bp = count_bp;
      nb_singles = count_singles;
    }

  return count_bp * size + count_singles;
}




/*
 *  COST_ON_VARIABLE
 *
 *  Evaluates the error on a variable.
 */

int
Cost_On_Variable(int i)
{
  return error[i];
}




void
Swap2(int i, int j)
{
  int w1 = sol_m[i];
  int w2 = sol_m[j];

  sol_m[i] = w2;
  sol_m[j] = w1;

  sol_w[w1] = j;
  sol_w[w2] = i;
}


#ifdef USE_NEXT_J

int Next_J(int i, int j, int exhaustive)
{
  return (j < 0) ? bp_swap[i] : -1;
}

#endif




/*
 *  COST_IF_SWAP
 *
 *  Evaluates the new total cost for a swap.
 */

int
Cost_If_Swap(int current_cost, int i, int j)
{
#ifndef USE_NEXT_J
  if (!(bp_swap[i] == j || bp_swap[j] == i)) /* only consider the worst bp */
    return current_cost;
#endif

  Swap2(i, j);
  int r = Cost_Of_Solution(0);
  Swap2(i, j);

  return r;
}




/*
 *  EXECUTED_SWAP
 *
 *  Records a swap.
 */

void
Executed_Swap(int i, int j)
{
  int w1 = sol_m[i];
  int w2 = sol_m[j];
  
  sol_w[w1] = i;		/* NB swap has already been done */
  sol_w[w2] = j;

  Cost_Of_Solution(1);
}




static inline int 
Find_Max(int prohibited_value) 
{
  int max_i = -1;		/* return -1 if none found */
  int max_err = 0;
  int max_nb = 0;
  int i;

  for(i = 0; i < size; i++)
    {
      int e = error[i];
      if (e == 0 || i == prohibited_value || bp_swap[i] == prohibited_value) 
	continue;

      if (e > max_err)
	{
	  max_i = i;
	  max_err = e;
	  max_nb = 1;
	} 
      else if (e == max_err && Random(++max_nb) == 0)
	{
	  max_i = i;
	}
    }

  return max_i;
}




/*
 *  RESET
 *
 * Performs a reset (returns the new cost or -1 if unknown)
 */
int
Reset(int n, AdData *p_ad)
{
  int max_i, bp_max_i;
  int other_i;

  if (nb_bp >= 1)		/* at least one BP */
    {
      max_i = Find_Max(-1);
      bp_max_i = bp_swap[max_i];
      Swap2(max_i, bp_swap[max_i]);
    
      /* find second max if possible (random is to avoid to be trapped in the same local min) */

      if (nb_bp >= 2 && Random_Double() < 0.98 && (other_i = Find_Max(bp_max_i)) >= 0)
	{
	  Swap2(other_i, bp_swap[other_i]);
	  return -1;
	}
    }

  /* here at most 1 swap has been done */

  if (nb_singles > 0)
    Swap2(single_i, Random(size));
  else
    Swap2(Random(size), Random(size));

  return -1;
}




/*
 *  SET_INIT_CONFIGURATION
 *
 *  Sets an initial configuration.
 */

void
Set_Init_Configuration(AdData *p_ad)
{
  int m;

  Random_Permut(sol_m, size, NULL, 0);

  for (m = 0; m < size; m++)
    sol_w[sol_m[m]] = m;
}




void
Check_Init_Configuration(AdData *p_ad)
{
  int i = Random_Permut_Check(p_ad->sol, p_ad->size, NULL, 0);
  if (i >= 0)
    {
      fprintf(stderr, "not a valid permutation, error at [%d] = %d\n", i, p_ad->sol[i]);
      Random_Permut_Repair(p_ad->sol, p_ad->size, p_ad->actual_value, p_ad->base_value);
      printf("possible repair:\n");
      Display_Solution(p_ad);
      exit(1);
    }
}


/*
 *  DISPLAY_SOLUTION
 *
 *  Displays a solution.
 */
void
Display_Solution(AdData *p_ad)
{
  int i;

  //  Ad_Display(p_ad->sol, p_ad, NULL); // to see actual values
  for(i = 0; i < p_ad->size; i++)
    {
      printf("%d ", p_ad->sol[i] + 1);
    }
  printf("\n");
}




int param_needed = -1;		/* overwrite var of main.c */


/*
 *  INIT_PARAMETERS
 *
 *  Initialization function.
 */

void
Init_Parameters(AdData *p_ad)
{
  char *end;
  p_ad->size = strtoul(p_ad->param_file, &end, 10);
  p_ad->data32[0] = 0;

  if (*end != '\0')				    /* not  a valid number */
    p_ad->size = SMP_Load_Problem(p_ad->param_file, NULL); /* get the problem size only */
  else
    p_ad->data32[0] = 1;

				/* defaults */
  if (p_ad->prob_select_loc_min == -1)
    p_ad->prob_select_loc_min = 100;

  if (p_ad->freeze_loc_min == -1)
    p_ad->freeze_loc_min = 1;

  if (p_ad->freeze_swap == -1)
    p_ad->freeze_swap = 0;

  if (p_ad->reset_limit == -1)
    p_ad->reset_limit = 1;

  if (p_ad->reset_percent == -1)
    p_ad->reset_percent = 0;	/* useless: customized reset */

  if (p_ad->restart_limit == -1)
    p_ad->restart_limit = 1000000000;

  if (p_ad->restart_max == -1)
    p_ad->restart_max = 10;
}


#undef Find_Rank_In_Pref_M
#undef Find_Rank_In_Pref_W
#define Find_Rank_In_Pref_M(m, w) Check_Find_Rank_In_Pref(pref_m, m, w)
#define Find_Rank_In_Pref_W(w, m) Check_Find_Rank_In_Pref(pref_w, w, m)


int
Check_Find_Rank_In_Pref(SMPMatrix pref_m, int m, int w)
{
  int k, z;
  int w1, rank;

  for(k = 0; (z = pref_m[m][k]) >= 0; k++)
    {
      Unpack(z, w1, rank);
      if (w == w1)
	return rank;
    }
  return -1;
}


/*
 *  CHECK_SOLUTION
 *
 *  Checks if the solution is valid.
 */

int
Check_Solution(AdData *p_ad)
{
  int m, w_of_m, rank_w_of_m;
  int w, m_of_w, rank_m_of_w, rank_w;
  int m1, rank_m1;
  int i, j, k, z;
  int count_singles = 0;
  int r = 1;
  int *sol_m, *sol_w;
  int size = p_ad->size;
  SMPMatrix pref_m = smp_info.pref_m;
  SMPMatrix pref_w = smp_info.pref_w;

  sol_m = p_ad->sol;

  i = Random_Permut_Check(sol_m, size, NULL, 0);
  
  if (i >= 0)
    {
      printf("ERROR: not a valid permutation, error at [%d] = %d\n", i, sol_m[i]);
      return 0;
    }

  sol_w = malloc(size * sizeof(*sol_w));
  if (sol_w == NULL)
    {
      fprintf(stderr, "%s:%d malloc failed\n", __FILE__, __LINE__);
      exit(1);
    }

  for (m = 0; m < size; m++)
    sol_w[sol_m[m]] = m;

  for (m = 0; m < size; m++)
    {
      w_of_m = sol_m[m];
      rank_w_of_m = Find_Rank_In_Pref_M(m, w_of_m); /* -1 is m is single */

      if (rank_w_of_m < 0)	/* man m is single */
	{
	  rank_w_of_m = size;	/* check all */
	  count_singles++;
	}

      for(k = 0; (z = pref_m[m][k]) >= 0; k++)
        {
	  Unpack(z, w, rank_w);
	  
	  if (rank_w >= rank_w_of_m) /* stop when rank of w is >= rank of curr partner of m */
	    break;

          m_of_w = sol_w[w];
	  rank_m_of_w = Find_Rank_In_Pref_W(w, m_of_w); /* -1 is m is single */
	  if (rank_w_of_m < 0)	/* man m is single */
	    {
	      rank_m_of_w = size;	/* check all */
	    }
          
          for(j = 0; (z = pref_w[w][j]) >= 0; j++)
            {
	      Unpack(z, m1, rank_m1);
	      if (rank_m1 >= rank_m_of_w) /* stop when rank of m1 is >= rank of curr partner of w */
		break;

              if (m1 == m)
                {
                  printf("ERROR: blocking pair %d - %d\n", m + 1, w + 1);
                  r = 0;
                  goto undominated_only; /* to only show undominated blocking-pair */
                }
            }
        }
    undominated_only:
      ;
    }

  free(sol_w);

  if (r && count_singles != 0)
    printf("Check Solution: warning there are %d singles\n", count_singles);

  return (r && count_singles == 0);
}
