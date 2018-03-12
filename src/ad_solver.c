/*
 *  Adaptive search
 *
 *  Copyright (C) 2002-2011 Daniel Diaz, Philippe Codognet and Salvador Abreu
 *
 *  ad_solver.c: general solver
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

#define AD_SOLVER_FILE

#include "ad_solver.h"
#include "tools.h"



/*-----------*
 * Constants *
 *-----------*/

#define BIG ((unsigned int) -1 >> 1)



/*-------*
 * Types *
 *-------*/

typedef struct
{
  int i, j;
}Pair;


/*------------------*
 * Global variables *
 *------------------*/

static AdData *p_ad ALIGN;	/* copy of the passed p_ad */

static int max_i ALIGN;		/* swap var 1: max projected cost (err_var[])*/
static int min_j ALIGN;		/* swap var 2: min conflict (swap[])*/
static int new_cost ALIGN;	/* cost after swapping max_i and min_j */
static int best_cost ALIGN;	/* best cost found until now */

static unsigned *mark ALIGN;	/* next nb_swap to use a var */
static int nb_var_marked ALIGN;	/* nb of marked variables */

#if defined(DEBUG) && (DEBUG&1)
static int *err_var;		/* projection of errors on variables */
static int *swap;		/* cost of each possible swap */
#endif

static int *list_i;		/* list of max to randomly chose one */
static int list_i_nb;		/* nb of elements of the list */

static int *list_j;		/* list of min to randomly chose one */
static int list_j_nb;		/* nb of elements of the list */

static Pair *list_ij;		/* list of max/min (exhaustive) */
static int list_ij_nb;		/* nb of elements of the list */

#ifdef LOG_FILE
static FILE *f_log;		/* log file */
#endif


//#define BASE_MARK    ((unsigned) p_ad->nb_iter)
#define BASE_MARK    ((unsigned) p_ad->nb_swap)
#define Mark(i, k)   mark[i] = BASE_MARK + (k)
#define UnMark(i)    mark[i] = 0
#define Marked(i)    (BASE_MARK + 1 <= mark[i])

#define USE_PROB_SELECT_LOC_MIN ((unsigned) p_ad->prob_select_loc_min <= 100)




/*------------*
 * Prototypes *
 *------------*/

#if defined(DEBUG) && (DEBUG&1)
static void Show_Debug_Info(void);
#endif

#undef DPRINTF

#if defined(DEBUG) && (DEBUG & 4)
#define DPRINTF(...) printf (__VA_ARGS__)
#else
#define DPRINTF(...) ((void) 0)
#endif



#if defined(DEBUG) && (DEBUG&1)
/*
 *  ERROR_ALL_MARKED
 */
static void
Error_All_Marked()
{
  int i;

  printf("\niter: %d - all variables are marked wrt base mark: %d\n",
	 p_ad->nb_iter, BASE_MARK);
  for (i = 0; i < p_ad->size; i++)
    printf("M(%d)=%d  ", i, mark[i]);
  printf("\n");
  exit(1);
}
#endif



/*
 * AD_UN_MARK
 */
void
Ad_Un_Mark(int i)
{
  UnMark(i);
}



/*
 *  SELECT_VAR_HIGH_COST
 *
 *  Computes err_swap and selects the maximum of err_var in max_i.
 *  Also computes the number of marked variables.
 */
static void
Select_Var_High_Cost(void)
{
  int i;
  int x, max;

  list_i_nb = 0;
  max = 0;
  nb_var_marked = 0;
  
  i = -1;
  while((unsigned) (i = Next_I(i)) < (unsigned) p_ad->size) // false if i < 0
    {
      if (Marked(i))
	{
#if defined(DEBUG) && (DEBUG&1)
	  err_var[i] = Cost_On_Variable(i);
#endif
	  nb_var_marked++;
	  continue;
	}

      x = Cost_On_Variable(i);
#if defined(DEBUG) && (DEBUG&1)
      err_var[i] = x;
#endif

      if (x >= max)
	{
	  if (x > max)
	    {
	      max = x;
	      list_i_nb = 0;
	    }
	  list_i[list_i_nb++] = i;
	}
    }

  /* here list_i_nb == 0 iff all vars are marked or bad Cost_On_Variable() */

#if defined(DEBUG) && (DEBUG&1)
  if (list_i_nb == 0)
    Error_All_Marked();
#endif

  p_ad->nb_same_var += list_i_nb;
  x = Random(list_i_nb);
  max_i = list_i[x];
}




/*
 *  SELECT_VAR_MIN_CONFLICT
 *
 *  Computes swap and selects the minimum of swap in min_j.
 */
static void
Select_Var_Min_Conflict(void)
{
  int j;
  int x;

 a:
  list_j_nb = 0;
  new_cost = p_ad->total_cost;

  j = -1;
  while((unsigned) (j = Next_J(max_i, j, 0)) < (unsigned) p_ad->size) // false if j < 0
    {
#if defined(DEBUG) && (DEBUG&1)
      swap[j] = Cost_If_Swap(p_ad->total_cost, j, max_i);
#endif

#ifndef IGNORE_MARK_IF_BEST
      if (Marked(j))
	continue;
#endif

      x = (max_i == j) ? p_ad->total_cost : Cost_If_Swap(p_ad->total_cost, j, max_i);
      /*
      printf("SWAPPING %d <=> %d (%d <=> %d) cost: %d => %d\n", j, max_i, p_ad->sol[j], p_ad->sol[max_i], p_ad->total_cost, x); 
      */

#ifdef IGNORE_MARK_IF_BEST
      if (Marked(j) && x >= best_cost)
	continue;
#endif

      if (USE_PROB_SELECT_LOC_MIN && j == max_i)
	continue;

      if (x <= new_cost)
	{
	  if (x < new_cost)
	    {
	      list_j_nb = 0;
	      new_cost = x;
	      if (p_ad->first_best)
		{
		  min_j = list_j[list_j_nb++] = j;
		  return;         
		}
	    }

	  list_j[list_j_nb++] = j;
	}
    }

  if (USE_PROB_SELECT_LOC_MIN)
    {
      if (new_cost >= p_ad->total_cost && 
	  (Random(100) < (unsigned) p_ad->prob_select_loc_min ||
	   (list_i_nb <= 1 && list_j_nb <= 1)))
	{
	  min_j = max_i;
	  return;
	}

      if (list_j_nb == 0)		/* here list_i_nb >= 1 */
	{
#if 0
	  min_j = -1;
	  return;
#else
	  p_ad->nb_iter++;
	  x = Random(list_i_nb);
	  max_i = list_i[x];
	  goto a;
#endif
	}
    }

  x = Random(list_j_nb);
  min_j = list_j[x];
}




/*
 *  SELECT_VARS_TO_SWAP
 *
 *  Computes max_i and min_j, the 2 variables to swap.
 *  All possible pairs are tested exhaustively.
 */
static void
Select_Vars_To_Swap(void)
{
  int i, j;
  int x;

  list_ij_nb = 0;
  new_cost = BIG;
  nb_var_marked = 0;

  i = -1;
  while((unsigned) (i = Next_I(i)) < (unsigned) p_ad->size) // false if i < 0
    {
      if (Marked(i))
	{
	  nb_var_marked++;
#ifndef IGNORE_MARK_IF_BEST
	  continue;
#endif
	}
      j = -1;
      while((unsigned) (j = Next_J(i, j, i + 1)) < (unsigned) p_ad->size) // false if j < 0
	{
#ifndef IGNORE_MARK_IF_BEST
	  if (Marked(j))
	    continue;
#endif
	  //	  printf("SWAP %d <-> %d\n", i, j);
	  x = Cost_If_Swap(p_ad->total_cost, i, j);
	  //	  printf("cost = %d\n", x);

#ifdef IGNORE_MARK_IF_BEST
	  if (Marked(j) && x >= best_cost)
	    continue;
#endif

	  if (x <= new_cost)
	    {
	      if (x < new_cost)
		{
		  new_cost = x;
		  list_ij_nb = 0;
		  if (p_ad->first_best == 1 && x < p_ad->total_cost)
		    {
		      max_i = i;
		      min_j = j;
		      return; 
		    }
		}
	      list_ij[list_ij_nb].i = i;
	      list_ij[list_ij_nb].j = j;
#if 0
	      if (list_ij_nb == p_ad->size - 1)
		printf("TRUNCATED !!!");
#endif
	      list_ij_nb = (list_ij_nb + 1) % p_ad->size;
	    }
	}
    }

  p_ad->nb_same_var += list_ij_nb;

#if 0
  if (new_cost >= p_ad->total_cost)
    printf("   *** LOCAL MIN ***  iter: %d  next cost:%d >= total cost:%d #candidates: %d\n", p_ad->nb_iter, new_cost, p_ad->total_cost, list_ij_nb);
#endif

  if (new_cost >= p_ad->total_cost)
    {
      if (list_ij_nb == 0 || 
	  (USE_PROB_SELECT_LOC_MIN && Random(100) < (unsigned) p_ad->prob_select_loc_min))
	{
	  for(i = 0; Marked(i); i++)
	    {
#if defined(DEBUG) && (DEBUG&1)
	      if (i > p_ad->size)
		Error_All_Marked();
#endif
	    }
	  max_i = min_j = i;
	  goto end;
	}

      if (!USE_PROB_SELECT_LOC_MIN && (x = Random(list_ij_nb + p_ad->size)) < p_ad->size)
	{
	  max_i = min_j = x;
	  goto end;
	}
    }

  x = Random(list_ij_nb);
  max_i = list_ij[x].i;
  min_j = list_ij[x].j;

 end:
#if defined(DEBUG) && (DEBUG&1)
  swap[min_j] = new_cost;
#else
  ;				/* anything for the compiler */
#endif
}




/*
 *  AD_SWAP
 *
 *  Swaps 2 variables.
 */
void
Ad_Swap(int i, int j)
{
  int x;

  p_ad->nb_swap++;
  x = p_ad->sol[i];
  p_ad->sol[i] = p_ad->sol[j];
  p_ad->sol[j] = x;
}




static void
Do_Reset(int n)
{
#if defined(DEBUG) && (DEBUG&1)
  if (p_ad->debug)
    printf(" * * * * * * RESET n=%d\n", n);
#endif

#ifdef TRACE
  printf(" * * * * * * RESET n=%d\n", n);
#endif

  int cost = Reset(n, p_ad);

#if UNMARK_AT_RESET == 2
  memset(mark, 0, p_ad->size * sizeof(unsigned));
#endif
  p_ad->nb_reset++;
  p_ad->total_cost = (cost < 0) ? Cost_Of_Solution(1) : cost;
}



/*
 *  EMIT_LOG
 *
 */
#ifdef LOG_FILE
#define Emit_Log(...)					\
  do if (f_log)						\
    {							\
      fprintf(f_log, __VA_ARGS__);			\
      fputc('\n', f_log);				\
      fflush(f_log);					\
  } while(0)
#else
#define Emit_Log(...)
#endif




/*
 *  AD_SOLVE
 *
 *  General solve function.
 *  returns the final total_cost (0 on success)
 */
int
Ad_Solve(AdData *p_ad0)
{
  int nb_in_plateau;

  p_ad = p_ad0;

  ad_sol = p_ad->sol; /* copy of p_ad->sol and p_ad->reinit_after_if_swap (used by no_cost_swap) */
  ad_reinit_after_if_swap = p_ad->reinit_after_if_swap;


  if (ad_no_cost_var_fct)
    p_ad->exhaustive = 1;


  mark = (unsigned *) malloc(p_ad->size * sizeof(unsigned));
  if (p_ad->exhaustive <= 0)
    {
      list_i = (int *) malloc(p_ad->size * sizeof(int));
      list_j = (int *) malloc(p_ad->size * sizeof(int));
    }
  else
    list_ij = (Pair *) malloc(p_ad->size * sizeof(Pair)); // to run on Cell limit to p_ad->size instead of p_ad->size*p_ad->size

#if defined(DEBUG) && (DEBUG&1)
  err_var = (int *) malloc(p_ad->size * sizeof(int));
  swap = (int *) malloc(p_ad->size * sizeof(int));
#endif

  if (mark == NULL || (!p_ad->exhaustive && (list_i == NULL || list_j == NULL)) || (p_ad->exhaustive && list_ij == NULL)
#if defined(DEBUG) && (DEBUG&1)
      || err_var == NULL || swap == NULL
#endif
      )
    {
      fprintf(stderr, "%s:%d: malloc failed\n", __FILE__, __LINE__);
      exit(1);
    }

  memset(mark, 0, p_ad->size * sizeof(unsigned)); /* init with 0 */

  int overall_best_cost = BIG;	/* this one is the best cost across restarts (best of best) */
  int *overall_best_sol = NULL;	/* this one is the best sol  across restarts (needed for optim_pb) */

  if (p_ad->optim_pb)
    {
      overall_best_sol = (int *) malloc(p_ad->size * sizeof(int));
      if (overall_best_sol == NULL)
	{
	  fprintf(stderr, "%s:%d: malloc failed\n", __FILE__, __LINE__);
	  exit(1);
	}
      memcpy(overall_best_sol, p_ad->sol, p_ad->size * sizeof(int));      
    }

#ifdef LOG_FILE
  f_log = NULL;
  if (p_ad->log_file)
    if ((f_log = fopen(p_ad->log_file, "w")) == NULL)
      perror(p_ad->log_file);
#endif

  p_ad->nb_restart = -1;

  p_ad->nb_iter = 0;
  p_ad->nb_swap = 0;
  p_ad->nb_same_var = 0;
  p_ad->nb_reset = 0;
  p_ad->nb_local_min = 0;

  p_ad->nb_iter_tot = 0;
  p_ad->nb_swap_tot = 0;
  p_ad->nb_same_var_tot = 0;
  p_ad->nb_reset_tot = 0;
  p_ad->nb_local_min_tot = 0;

#if defined(DEBUG) && (DEBUG&2)
  if (p_ad->do_not_init)
    {
      printf("********* received data (do_not_init=1):\n");
      Ad_Display(p_ad->sol, p_ad, NULL);
      printf("******************************-\n");
    }
#endif

  if (!p_ad->do_not_init)
    {
    restart:
      p_ad->nb_iter_tot += p_ad->nb_iter; 
      p_ad->nb_swap_tot += p_ad->nb_swap; 
      p_ad->nb_same_var_tot += p_ad->nb_same_var;
      p_ad->nb_reset_tot += p_ad->nb_reset;
      p_ad->nb_local_min_tot += p_ad->nb_local_min;

      Set_Init_Configuration(p_ad);
      memset(mark, 0, p_ad->size * sizeof(unsigned)); /* init with 0 */
    }

  p_ad->nb_restart++;
  p_ad->nb_iter = 0;
  p_ad->nb_swap = 0;
  p_ad->nb_same_var = 0;
  p_ad->nb_reset = 0;
  p_ad->nb_local_min = 0;


  nb_in_plateau = 0;

  best_cost = p_ad->total_cost = Cost_Of_Solution(1);

  while(!TARGET_REACHED(p_ad))
    {
      //if (p_ad->total_cost < 3150000) 	printf("\nI found: %d\n\n", p_ad->total_cost);
      if (p_ad->total_cost < overall_best_cost && p_ad->total_cost > p_ad->target_cost)
	{
	  overall_best_cost = p_ad->total_cost;
#if 0 //****************************** OPTIM problem
	  printf("exec: %3d  iter: %10d  BEST %d (#locmin:%d  resets:%d)\n",  p_ad->nb_restart, p_ad->nb_iter, overall_best_cost, p_ad->nb_local_min, p_ad->nb_reset);
	  Display_Solution(p_ad);
#endif
	  if (overall_best_sol)
	    memcpy(overall_best_sol, p_ad->sol, p_ad->size * sizeof(int));      
	}

      p_ad->nb_iter++;

      if (p_ad->nb_iter >= p_ad->restart_limit)
	{
	  if (p_ad->nb_restart < p_ad->restart_max)
	    goto restart;
	  break;
	}

      if (!p_ad->exhaustive)
	{
	  Select_Var_High_Cost();
	  Select_Var_Min_Conflict();
	}
      else
	{
	  Select_Vars_To_Swap();
	}

      Emit_Log("----- iter no: %d, cost: %d, nb marked: %d ---",
	       p_ad->nb_iter, p_ad->total_cost, nb_var_marked);
      /*
	printf("----- iter no: %d, cost: %d, nb marked: %d --- swap: %d/%d  nb pairs: %d  new cost: %d\n", 
	p_ad->nb_iter, p_ad->total_cost, nb_var_marked,
	max_i, min_j, list_ij_nb, new_cost);
      */
      /* Display_Solution(p_ad); */

#ifdef TRACE
      printf("----- iter no: %d, cost: %d, nb marked: %d --- swap: %d/%d  nb pairs: %d  new cost: %d\n", 
             p_ad->nb_iter, p_ad->total_cost, nb_var_marked,
             max_i, min_j, list_ij_nb, new_cost);
#endif
#ifdef TRACE
      Display_Solution(p_ad);
#endif

      if (p_ad->total_cost != new_cost)
	{
	  if (nb_in_plateau > 1)
	    {
	      Emit_Log("\tend of plateau, length: %d", nb_in_plateau);
	    }
	  nb_in_plateau = 0;
	}

      if (new_cost < best_cost)
	{
	  best_cost = new_cost;
	}


      if (!p_ad->exhaustive)
	{
	  Emit_Log("\tswap: %d/%d  nb max/min: %d/%d  new cost: %d",
		   max_i, min_j, list_i_nb, list_j_nb, new_cost);
	}
      else
	{
	  Emit_Log("\tswap: %d/%d  nb pairs: %d  new cost: %d",
		   max_i, min_j, list_ij_nb, new_cost);
	}


#if defined(DEBUG) && (DEBUG&1)
      if (p_ad->debug)
	Show_Debug_Info();
#endif

#if 0
      if (new_cost >= p_ad->total_cost && nb_in_plateau > 15)
	{
	  Emit_Log("\tTOO BIG PLATEAU - RESET");
	  Do_Reset(p_ad->nb_var_to_reset);
	}
#endif
      nb_in_plateau++;

      if (min_j == -1)
	continue;

      if (max_i == min_j)
	{
	  p_ad->nb_local_min++;
	  Mark(max_i, p_ad->freeze_loc_min);

	  if (nb_var_marked + 1 >= p_ad->reset_limit)
	    {
	      Emit_Log("\tTOO MANY FROZEN VARS - RESET");
	      Do_Reset(p_ad->nb_var_to_reset);
	    }
	}
      else
	{
#if 1
	  Mark(max_i, p_ad->freeze_swap);
	  Mark(min_j, p_ad->freeze_swap);
#else
	  if (Random_Double() < 0.5)
	    Mark(max_i, p_ad->freeze_swap);
	  else
	    Mark(min_j, p_ad->freeze_swap);
#endif
	  Ad_Swap(max_i, min_j);
	  p_ad->total_cost = new_cost;
	  Executed_Swap(max_i, min_j);
	}
    }

#ifdef LOG_FILE
  if (f_log)
    fclose(f_log);
#endif

  free(mark);
  free(list_i);
  if (!p_ad->exhaustive)
    free(list_j);
  else
    free(list_ij);

#if defined(DEBUG) && (DEBUG&1)
  free(err_var);
  free(swap);
#endif


  if (overall_best_cost < p_ad->total_cost && overall_best_sol)
    {
      memcpy(p_ad->sol, overall_best_sol, p_ad->size * sizeof(int));
      p_ad->total_cost = overall_best_cost;
    }

  if (overall_best_sol)
    free(overall_best_sol);

  p_ad->nb_iter_tot += p_ad->nb_iter; 
  p_ad->nb_swap_tot += p_ad->nb_swap; 
  p_ad->nb_same_var_tot += p_ad->nb_same_var;
  p_ad->nb_reset_tot += p_ad->nb_reset;
  p_ad->nb_local_min_tot += p_ad->nb_local_min;

  return p_ad->total_cost;
}



/*
 *  AD_DISPLAY
 *
 */
void
Ad_Display(int *t, AdData *p_ad, unsigned *mark)
{
  int i, k = 0, n;
  char buff[100];

  sprintf(buff, "%d", p_ad->base_value + p_ad->size - 1);
  n = strlen(buff);
  
  for(i = 0; i < p_ad->size; i++)
    {
      printf("%*d", n, t[i]);
      if (mark)
	{
	  if (Marked(i))
	    printf(" X ");
	  else
	    printf("   ");
	}
      else
	printf(" ");

      if (++k == p_ad->break_nl)
	{
	  putchar('\n');
	  k = 0;
	}
    }
  if (k)
    putchar('\n');
}




/*
 *  SHOW_DEBUG_INFO
 *
 *  Displays debug info.
 */
#if defined(DEBUG) && (DEBUG&1)
static void
Show_Debug_Info(void)
{
  char buff[100];

  printf("\n--- debug info --- iteration no: %d  swap no: %d\n", p_ad->nb_iter, p_ad->nb_swap);
  Ad_Display(p_ad->sol, p_ad, mark);
  if (!ad_no_displ_sol_fct)
    {
      printf("user defined Display_Solution:\n");
      Display_Solution(p_ad);
    }
  printf("total_cost: %d\n\n", p_ad->total_cost);
  if (!p_ad->exhaustive)
    {
      Ad_Display(err_var, p_ad, mark);
      printf("chosen for max error: %d, error: %d\n\n",
	     max_i, err_var[max_i]);
      Ad_Display(swap, p_ad, mark);
      printf("chosen for min conflict: %d, cost: %d\n",
	     min_j, swap[min_j]);
    }
  else
    {
      printf("chosen for swap: %d<->%d, cost: %d\n", 
	     max_i, min_j, swap[min_j]);
    }

  if (max_i == min_j)
    printf("\nfreezing var %d for %d swaps\n", max_i, p_ad->freeze_loc_min);

  if (p_ad->debug == 2)
    {
      printf("\nreturn: next step, c: continue (as with -d), s: stop debugging, q: quit: ");
      if (fgets(buff, sizeof(buff), stdin)) /* avoid gcc warning warn_unused_result */
	{}
      switch(*buff)
	{
	case 'c':
	  p_ad->debug = 1;
	  break;
	case 's':
	  p_ad->debug = 0;
	  break;
	case 'q':
	  exit(1);
	}
    }
}
#endif


