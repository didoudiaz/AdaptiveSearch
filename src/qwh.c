/*
 *  Adaptive search
 *
 *  Copyright (C) 2002-2011 Daniel Diaz, Philippe Codognet and Salvador Abreu
 *
 *  qwh.c: the Quasigroup With Holes Problem
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "ad_solver.h"


#if 1
#define ALL_DIFF
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

static int size;		/* copy of p_ad->size (size = nb_hole) */
static int *sol;		/* copy of p_ad->sol */


typedef unsigned long long BitVec;

#define BV_FULL(size)                   (((BitVec) 1 << size) - 1)

#define BV_Full(vec, size)              (vec = BV_FULL(order))
#define BV_Complement(vec, vec1, size)  (vec = BV_FULL(order) & ~(vec1))
#define BV_Empty(vec)                   (vec = (BitVec) 0)
#define BV_Is_Empty(vec)                (vec == (BitVec) 0)
#define BV_Set_Value(vec, x)            (vec |= ((BitVec) 1 << (x)))
#define BV_Reset_Value(vec, x)          (vec &= ~((BitVec) 1 << (x)))
#define BV_Has_Value(vec, x)            ((vec & ((BitVec) 1 << (x))) != (BitVec) 0)
#define BV_First_Value(vec)             (__builtin_ffsll(vec) - 1)
#define BV_Cardinality(vec)             __builtin_popcountll(vec)
#define BV_Equal(vec1, vec2)            ((vec1) == (vec2))
#define BV_Intersect(vec, vec1, vec2)   ((vec) = (vec1) & (vec2))
#define BV_Includes(vec1, vec2)         ((vec1) | (vec2) == (vec1))

	/* NB: BV_FOREACH uses vec which will be modified (0 at the end if no break instruction) */

#define  BV_FOREACH(vec, x)			\
  for((x) = 0; (vec) != 0; (vec) >>= 1, (x)++)	\
    if (((vec) & 1) != 0)



#define MAX_ORDER   50
#define MAX_SIZE    (MAX_ORDER * MAX_ORDER)


/* Data of the problem */

typedef struct
{
  int i;
  int l, c;
  int dom_size;
  BitVec bv_dom;

#ifdef ALL_DIFF			/* data for the all-diff constraint */

  BitVec ad_bv_dom;		/* domain */
  int ad_dom_size;		/* domain cardinality */

  int ad_propag_me_timestamp;	/* should be propagated ? */

  BitVec ad_sos_bv_dom;		/* save of the domain (for undo) */
  int ad_sos_dom_size;		/* save of the domain cardinality */
  int ad_save_timestamp;	/* date of the save */
#endif
} InfHole;


typedef struct
{
  int val[MAX_ORDER];		/* [0..order-1]: fixed value or -index - 1 for a hole */
  int beg_i;			/* start index (missing vals are in sol[beg_i]..sol[next_i - 1]) */
  int next_i;			/* start index of next line = beg_i + nb_hol */
  int nb_hol;			/* nb of holes in the line (i.e. nb of missing values) */
  int hole_val[MAX_ORDER];	/* [0..nb_hol]: missing values (used for initial random permut) */
  BitVec bv_missing_val;	/* bit-vector of missing values */
  BitVec bv_where[MAX_ORDER];	/* [0..order-1]: bv_where[x] = bit-vector of cols where x can appear */
  BitVec bv_missing_col;	/* bit-vector of missing columns */
} InfLin;

typedef struct
{
  int fixed[MAX_ORDER];		/* [0..order-1]: fixed[x] = 1 if x is fixed, 0 otherwise */
  int nb_hol;			/* nb of holes in the col */
  InfHole *hol[MAX_ORDER];	/* [0..nb_hol-1]: info on each hole */
  BitVec bv_missing_val;	/* bit-vector of missing values */
  BitVec bv_where[MAX_ORDER];	/* [0..order-1]: bv_where[x] = bit-vector of lines where x can appear */
} InfCol;


static int order = -1;		/* order of the problem (size of the square side) */

static int nb_hole_orig;	/* nb of holes in the original problem */
static int nb_hole;		/* nb of holes */
static InfHole hol[MAX_SIZE];	/* the holes */
static int max_dom_size;	/* biggest domain size */

static InfLin lin[MAX_ORDER];	/* the lines (rows) */
static InfCol col[MAX_ORDER];	/* the columns */

static int count[MAX_ORDER];


int reinit_pool = 1;

static int trace = -1;


/*------------*
 * Prototypes *
 *------------*/

#ifdef ALL_DIFF

void All_Diff_Init(void);

int All_Diff_Tell_Domain(int i, BitVec bv_dom);

int All_Diff_Tell_Value(int i, int x);

int All_Diff_Do_Propagation(void);

void All_Diff_Undo();

#endif


void Display_Solution(AdData *p_ad);
void Display_Solution_Color(AdData *p_ad);
int Check_Solution(AdData *p_ad);
int Check_Solution_Line(AdData *p_ad);
void Display_Vector(BitVec vec);

/*
 *  MODELING
 */

void
PLS_Load_Problem(char *file)
{
  FILE *f;
  int l, c, x, i, j, n;
  BitVec bv_tmp;
  static char buff[1024];
      
  if ((f = fopen(file, "r")) == NULL)
    {
      perror(file);
      exit(1);
    }

  do
    if (fscanf(f, "%s %d", buff, &order) != 2)
      {
	printf("%s: Bad file format (cannot read the order)\n", file);
	exit(1);
      }
  while(strcmp(buff, "order") != 0);



  for(c = 0; c < order; c++)
    {
      col[c].nb_hol = 0;
      BV_Full(col[c].bv_missing_val, order);
    }


  i = 0;

  for(l = 0; l < order; l++)
    {
      lin[l].beg_i = i;
      lin[l].bv_missing_col = 0;

      BV_Full(lin[l].bv_missing_val, order);
      
      for(c = 0; c < order; c++)
	{
	  BV_Empty(lin[l].bv_where[c]); /* c here is in fact x (simply used to reset all bv_where[l][...] */
	  BV_Empty(lin[c].bv_where[l]); /* l here is in fact x (simply used to reset all bv_where[c][...] */

	  if (fscanf(f, "%d", &x) != 1)
	    {
	      printf("%s: Bad file format (order: %d cannot read value[%d][%d])\n", file, order, l, c);
	      exit(1);
	    }
 
	  if (x < 0)
	    {
	      lin[l].val[c] = -i - 1;

	      hol[i].i = i;
	      hol[i].l = l;
	      hol[i].c = c;

	      BV_Full(hol[i].bv_dom, order);

	      col[c].hol[col[c].nb_hol++] = &hol[i];

	      i++;	      
	    }
	  else
	    {
	      lin[l].val[c] = x;

	      BV_Reset_Value(lin[l].bv_missing_val, x);
	      BV_Reset_Value(col[c].bv_missing_val, x);
	    }
	}
      lin[l].next_i = i;
      lin[l].nb_hol = i - lin[l].beg_i;
    }
  fclose(f);

  nb_hole = nb_hole_orig = i;

  for(i = 0; i < nb_hole_orig; i++)
    {
      l = hol[i].l;
      hol[i].bv_dom = lin[l].bv_missing_val;
      hol[i].dom_size = BV_Cardinality(hol[i].bv_dom);
    }


#ifdef ALL_DIFF

  /* preprocess to reduce domains */

  for(i = 0; i < nb_hole_orig; i++)
    {
      hol[i].ad_bv_dom = hol[i].bv_dom;
      hol[i].ad_dom_size = hol[i].dom_size;
    }

  All_Diff_Init();

  for(i = 0; i < nb_hole_orig; i++)
    {
      l = hol[i].l;
      c = hol[i].c;

      BV_Intersect(bv_tmp, lin[l].bv_missing_val, col[c].bv_missing_val);

      if (!All_Diff_Tell_Domain(i, bv_tmp))
	{
	unsolvable:		/* should not occurs in QWH ! */
	  printf("Unsolvable problem\n");
	  exit(1);
	}
    }
  if (!All_Diff_Do_Propagation())
    goto unsolvable;

  i = 0;
  for(j = 0; j < nb_hole_orig; j++)
    {
      l = hol[j].l;
      c = hol[j].c;

      if (hol[j].ad_dom_size == 1) /* fixed, no longer a hole */
	{
	  x = BV_First_Value(hol[j].ad_bv_dom);

	  lin[l].val[c] = x;

	  BV_Reset_Value(lin[l].bv_missing_val, x);
	  BV_Reset_Value(col[c].bv_missing_val, x);
	  if (trace)
	    printf("fix value [%3d] %2d/%-2d = %2d\n", j, l, c, x);
	}
      else
	{			/* a real hole: copy it and correct it */
	  hol[i] = hol[j];
	  hol[i].i = i;		/* fix i */
	  hol[i].bv_dom = hol[i].ad_bv_dom;
	  hol[i].dom_size = hol[i].ad_dom_size;

	  lin[l].val[c] = -i - 1;

	  i++;
	}
    }
  nb_hole = i;

#endif	/* ALL_DIFF */


  for(c = 0; c < order; c++)
    {
      col[c].nb_hol = 0;
    }

  max_dom_size = 0;
  i = 0;
  for(l = 0; l < order; l++)
    {
      lin[l].beg_i = i;
      BV_Empty(lin[l].bv_missing_col);

      for(c = 0; c < order; c++)
        {
          x = lin[l].val[c];
          if (x >= 0)
	    {
	      col[c].fixed[x] = 1;
	      continue;
	    }

	  j = -x - 1;

	  n = hol[j].dom_size;

	  if (n > max_dom_size)
	    max_dom_size = n;

	  col[c].hol[col[c].nb_hol++] = &hol[i];

	  BV_Set_Value(lin[l].bv_missing_col, c);
	  bv_tmp = hol[i].bv_dom;
	  BV_FOREACH(bv_tmp, x)
	    {
	      BV_Set_Value(lin[l].bv_where[x], c);
	      BV_Set_Value(col[c].bv_where[x], l);
	    }

	  i++;
	}

      int k = 0;
      bv_tmp = lin[l].bv_missing_val;
      BV_FOREACH(bv_tmp, x)
	{
	  lin[l].hole_val[k++] = x;
	}

      lin[l].next_i = i;
      lin[l].nb_hol = i - lin[l].beg_i; /* nb of holes in this line */
    }


#if 0

  printf("********** DEBUG INFO **********\n\n");
  printf("Order: %d  nb hole orig:%d   nb hole: %d\n", order, nb_hole_orig, nb_hole);
  printf("\nLine Info:  value < 0 if hole (index = -value - 1)\n");
  for(l = 0; l < order; l++)
    {
      printf("   line %2d: value:", l);
      for(c = 0; c < order; c++)
	printf(" %3d", lin[l].val[c]);
      printf(" | beg_i: %2d  next_i: %2d nb_hol: %2d  missing values: {", 
	     lin[l].beg_i, lin[l].next_i, lin[l].nb_hol);

      for(n = 0; n < lin[l].nb_hol; n++)
	printf(" %2d", lin[l].hole_val[n]);
      printf("}");
      // printf(" BV missing val: "); Display_Vector(lin[l].bv_missing_val);
      // printf(" BV missing col: "); Display_Vector(lin[l].bv_missing_col);
      // printf(" BV where: "); Display_Vector(lin[l].bv_missing_col);
      printf("\n");

    }

  printf("\nCol. Info:  fixed[x] != 0 if x is fixed\n");
  for(c = 0; c < order; c++)
    {
      printf("   col. %2d: fixed:", c);
      for(l = 0; l < order; l++)
	printf(" %d", col[c].fixed[l]);
      printf(" | nb_hol: %2d  var indexes: {", col[c].nb_hol);
      for(n = 0; n < col[c].nb_hol; n++)
	printf(" %2d", col[c].hol[n]->i);
      printf("}");
      //printf(" BV missing val: "); Display_Vector(col[c].bv_missing_val);
      printf("\n");
    }

  printf("\nLine Missing value domains (for each value -> set of possible cols):\n");
  for(l = 0; l < order; l++)
    {
      printf("   line %2d:", l);
      for(x = 0; x < order; x++)
	{
	  if (!BV_Is_Empty(lin[l].bv_where[x]))
	    {
	      printf(" %d =", x);
	      Display_Vector(lin[l].bv_where[x]);
	    }
	}
      printf("\n");
    }

  printf("\nCol. Missing value domains (for each value -> set of possible lines):\n");
  for(c = 0; c < order; c++)
    {
      printf("   col. %2d:", c);
      for(x = 0; x < order; x++)
	{
	  if (!BV_Is_Empty(col[c].bv_where[x]))
	    {
	      printf(" %d =", x);
	      Display_Vector(col[c].bv_where[x]);
	    }
	}
      printf("\n");
    }

  printf("\nHole Info:\n");

  for(i = 0; i < nb_hole; i++)
    {
      printf("   hole[%2d]: %2d/%-2d  dom: nb:%2d ", i, hol[i].l, hol[i].c, BV_Cardinality(hol[i].bv_dom));
      Display_Vector(hol[i].bv_dom);
      printf("\n");
    }
  printf("\n");

  printf("********************************\n");

  exit(1);

#endif
  

#if 1				/* .qwh generation */
  sprintf(buff, "PLS/pb-%d-%d.qwh", order, nb_hole);
  f = fopen(buff, "w");
  fprintf(f, "order %d\n", order);
  fprintf(f, "holes %d\n", nb_hole);

  for(l = 0; l < order; l++)
    {
      for(c = 0; c < order; c++)
	{
	  x = lin[l].val[c];
	  if (x < 0)
	    x = -1;
	  fprintf(f, " %3d", x);
	}
      fprintf(f, "\n");
    }
      

  //  printf("\n");
  for(i = 0; i < nb_hole; i++)
    {
      fprintf(f, "%2d", hol[i].dom_size);
      bv_tmp = hol[i].bv_dom;
      BV_FOREACH(bv_tmp, x)
	{
	  fprintf(f, " %2d", x);
	}
      fprintf(f, "\n");
    }
  fclose(f);
#endif
  
#if 1				/* .pls generation */
  sprintf(buff, "PLS/pb-%d-%d.pls", order, nb_hole);
  f = fopen(buff, "w");
  fprintf(f, "order %d\n", order);

  for(l = 0; l < order; l++)
    {
      for(c = 0; c < order; c++)
	{
	  x = lin[l].val[c];
	  if (x < 0)
	    x = -1;
	  fprintf(f, " %3d", x);
	}
      fprintf(f, "\n");
    }      
  fclose(f);
#endif
  

}

static AdData *p_ad0;

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

  p_ad0 = p_ad;

  if (order < 0)
    PLS_Load_Problem(p_ad->param_file);

  reinit_pool = 1;
  Ad_Solve(p_ad);
}



void
Set_Init_Configuration(AdData *p_ad)
{
  int l, n;

  sol = p_ad->sol;

  if (order < 0)		/* in case it is called by main() and not by ad_solver */
    PLS_Load_Problem(p_ad->param_file);

  
  for(l = 0; l < order; l++)
    {
      n = lin[l].nb_hol;
#if 1
      if (n)
	Random_Permut(sol + lin[l].beg_i, n, lin[l].hole_val, 0);
#else
      if (n)
	memcpy(sol + lin[l].beg_i, lin[l].hole_val, n * sizeof(int));
#endif
    }

#if 0
  printf("initial configuration:\n");
  Display_Solution_Color(p_ad);
#if 0
  if (Check_Solution(p_ad0) == 0)
    {
      printf("bad init\n");
      exit(1);
    }
#endif
#endif
}


void
Check_Init_Configuration(AdData *p_ad)
{
  printf("Not yet implemented. TAKE CARE !!!\n");
}






inline int Sq(int x) { return x*x;} 

inline int Min(int x, int y) { return x < y ? x : y;} 
inline int Max(int x, int y) { return x > y ? x : y;} 

int miss_nb;


static int var_err[MAX_SIZE];
static int ivar_err[MAX_SIZE];
static int first[MAX_ORDER];
static int nb_col_err;
static int col_err[MAX_ORDER];
static int icol_err[MAX_ORDER];
static int nb_var_err;

BitVec bv_on_error;

int
Compute_Errors(int *err)
{
  int c, l, i, n, x;
  int nb_dom_err = 0;
  int r = 0;
  
#if 0
  int Check_Solution_Line(AdData *p_ad);
  if (Check_Solution_Line(p_ad0) == 0)
    {
      Display_Solution_Color(p_ad0);
      exit(1);
    }
#endif

  int err_reach = 0;

  nb_col_err = 0;
  int max_ierr = 0;

  bv_on_error = 0;

  if (err)
    {
      memset(err, 0, size * sizeof(int));
      nb_var_err = 0;
    }

  for(c = 0; c < order; c++)
    {
      memcpy(count, col[c].fixed, order * sizeof(int));

      n = col[c].nb_hol;

      int rc = 0;

      col_err[c] = -1;

      BitVec bv_can_be_reach;
      BV_Empty(bv_can_be_reach);
      BitVec bv_missing = col[c].bv_missing_val;

      int beg_ivar = nb_var_err;

      while(n)
	{
	  InfHole *ph = col[c].hol[--n];

	  i = ph->i;
	  l = ph->l;

	  x = sol[i];

	  count[x]++;
	  BV_Reset_Value(bv_missing, x);

	  if (!BV_Has_Value(ph->bv_dom, x))
	    {
	      if (err)
		{
		  var_err[i]++;
		  ivar_err[nb_var_err++] = i;
		}
	      BV_Set_Value(bv_on_error, x);
	      bv_can_be_reach |= ph->bv_dom;
	      nb_dom_err++;
	      // rc+=max_dom_size - BV_Cardinality(ph->bv_dom) + 1;
	      rc++;
	    }

	  if (count[x] == 1)
	    first[x] = i;
	  else
	    {
	      BV_Set_Value(bv_on_error, x);
	      bv_can_be_reach |= ph->bv_dom;

	      if (hol[i].l > max_ierr)
		max_ierr = hol[i].l;
	      rc++;
	      if (err)
		{
		  var_err[i]++;
		  if (count[x] == 2)
		    {
		      var_err[first[x]]++;
		      //ivar_err[nb_var_err++] = (Random_Double() < 0.5) ? first[x] : i;
		      ivar_err[nb_var_err++] = first[x]; ivar_err[nb_var_err++] = i;
		      //ivar_err[nb_var_err++] = i;//first[x]; ivar_err[nb_var_err++] = i;
		    }
		}
	    }
	}

      if (rc)
	{
	  icol_err[nb_col_err++] = c;
	  r += rc;

	  for(x = 0; x < order; x++)
	    {
	      if (count[x] == 0)
		{
		  col_err[c] = x;	/* missing value */
		  int k;
		  for(k = beg_ivar; k < nb_var_err; k++)
		    {
		      i = ivar_err[k];
		      int x1 = sol[i];
		      l = hol[i].l;
		      if (!BV_Has_Value(hol[i].bv_dom, x))
			continue;

		      int i0;
		      for(i0 = lin[l].beg_i; i0 < lin[l].next_i; i0++)
			if (sol[i0] == x)
			  {
			    int c0 = hol[i0].c;
			    if (col[c0].fixed[x1] == 1)
			      err_reach+=4;
			    k = nb_var_err;
			    goto ok_for_this_missing_value;
			  }
		    }
		  err_reach += order;
		}
	    ok_for_this_missing_value:
	      ;
	    }
	}
    }


  //r = r  + 2*nb_dom_err;

  //r = r  * 2 + nb_dom_err;

  r = r + err_reach + order * nb_dom_err;

#if 0
  if (err_reach && r <= 6)
    {
      printf("**************** OCCURS: cost: %d  err_reach:%d\n", r, err_reach);
      Display_Solution_Color(p_ad0);
      // exit(1);
    }
#endif
  return r;
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
  int r = Compute_Errors((should_be_recorded) ? var_err : NULL);

#if 0
  int Check_Solution_Line(AdData *p_ad);
  if (Check_Solution_Line(p_ad0) == 0)
    {
      Display_Solution_Color(p_ad0);
      exit(1);
    }
#endif

#ifdef TRACE
  if (should_be_recorded)
    printf("cost: %-4d ", r);
#endif

 return r;
}


#if 0

#define COST_ON_VARIABLE
/*
 *  COST_ON_VARIABLE
 *
 *  Evaluates the error on a variable.
 */
int
Cost_On_Variable(int i)
{
  return var_err[i];
}

#endif

#if 0

/*
 *  COST_IF_SWAP
 *
 *  Evaluates the new total cost for a swap.
 */

int
Cost_If_Swap(int current_cost, int i, int j)
{
  //printf("%d <-> %d   %d/%d <-> %d/%d\n", i, j, hol[i].l, hol[i].c, lin_of[j], col_of[j]);

  if (hol[i].l != hol[j].l)
    exit(1);
  int x;
  int r;

  x = ad_sol[i];
  ad_sol[i] = ad_sol[j];
  ad_sol[j] = x;

  r = Cost_Of_Solution(0);

  ad_sol[j] = ad_sol[i];
  ad_sol[i] = x;

  if (ad_reinit_after_if_swap)
    Cost_Of_Solution(0);

  return r;
}

#endif

#if 1
/*
 *  EXECUTED_SWAP
 *
 *  Records a swap.
 */

void
Executed_Swap(int i1, int i2)
{
  Cost_Of_Solution(1);
}
#endif

/*
 *  NEXT_J
 *
 *  Return the next pair i/j to try.
 */

int Next_J(int i, int j)
{
  int l = hol[i].l;

#ifndef COST_OF_SOLUTION				/* for exhaustive */
  if (j < 0)
    j = i;
#else
  if (j < 0)
    j = lin[l].beg_i - 1;		/* for use with Cost_On_Variable */
#endif
  j++;


  if (j >= lin[l].next_i)
    j = size;			/* stop now */

  return j;
}



/*
 *  RESET
 *
 * Performs a reset (returns the new cost or -1 if unknown or some other data are not updated)
 *
 */


int
Reset_Lines_Error(int n, AdData *p_ad)
{
  int i, j, k, x;
  int nh;
  int l;
  // int z;

#if 0
  for(k = 0; k < nb_var_err; k++)
    printf(" %d", ivar_err[k]);
  printf("\n");
#endif

  p_ad->total_cost = Compute_Errors(var_err);

  Random_Array_Permut(ivar_err, nb_var_err);

 #if 0
  for(k = 0; k < nb_var_err; k++)
    printf(" %d", ivar_err[k]);
  printf("\n");
#endif

  for(k = 0; k < nb_var_err; k++)
    {
      i = ivar_err[k];
      l = hol[i].l;

      nh = lin[l].nb_hol;

      //for(z = 3; z > 0; z--)
	{
	  do
	    j = lin[l].beg_i + Random(nh);
	  while(i == j);// ||

	  // if (col_err[col_of[j]] < 0) continue;

	  n--;
	  p_ad->nb_swap++;

	  x = sol[i];
	  sol[i] = sol[j];
	  sol[j] = x;

#if UNMARK_AT_RESET == 1
	  Ad_Un_Mark(i);
	  Ad_Un_Mark(j);
#endif

	  i = lin[l].beg_i + Random(nh);
	  //i = j;
	}

      if (n < 0)	break;
    }
  return n;
}



int
Reset_Repair(int n, AdData *p_ad)
{
  int i, j, k, nh, u, l, c;
  int mod = 0;

  static int save_sol[100000];
  memcpy(save_sol, sol, size * sizeof(int));

  p_ad->total_cost = Compute_Errors(var_err);

  for(k = 0; k < nb_var_err; k++)
    {
      i = ivar_err[k];
      l = hol[i].l;
      c = hol[i].c;

      for(j = lin[l].beg_i; j < lin[l].next_i; j++)
	{
	  sol[j] = -1;
	  mod++;
	}
      
      nh = col[c].nb_hol;
      for(u = 0; u < nh; u++)
	{
	  sol[col[c].hol[u]->i] = -1;
	  mod++;
	}
    }

  for(l = 0; l < order; l++)
    Random_Permut_Repair(sol + lin[l].beg_i, lin[l].nb_hol, lin[l].hole_val, 0);

#if 1 
  int diff = 0;
  for(i = 0; i < size; i++)
    if (sol[i] != save_sol[i])
      diff++;

  diff /= 4;
  n -= diff;
  
#endif
  return n;
}



#ifdef ALL_DIFF

static void
Partial_Repair_FF(void)
{
  int i, x;

#if 1
  for(i = 0; i < nb_hole; i++)
    {
      hol[i].ad_bv_dom = hol[i].bv_dom;
      hol[i].ad_dom_size = hol[i].dom_size;
      hol[i].ad_save_timestamp = 0;
    }
#endif

  //  timestamp = 0;

  static int done[MAX_SIZE];
  memset(done, 0, nb_hole * sizeof(int));

  for(;;)
    {
      int min_i = 0;
      int min_dom_size = order + 1;
      int min_nb = 0;


      /* first-fail: choose variable with smallest domain */

      for(i = 0; i < nb_hole; i++)
        {
          if (done[i] || sol[i] == -1)
            continue;

          int n = hol[i].dom_size;
          if (n < min_dom_size)
            {
              min_dom_size = n;
              min_i = i;
              min_nb = 1;
            }
          else if (n == min_dom_size && Random(++min_nb) == 0)
            min_i = i;
        }
      if (min_nb == 0)
        break;

      i = min_i;
      done[i] = 1;

      All_Diff_Init();

#if 1
      if (hol[i].ad_dom_size == 1)
	sol[i] = BV_First_Value(hol[i].ad_bv_dom);
#endif
      x = sol[i];

#if 0
      if (trace)
	{
	  printf("trying to set [%3d] %2d/%-2d = %d dom: size:%d ", i, hol[i].l, hol[i].c, x, hol[i].ad_dom_size);
	  Display_Vector(hol[i].ad_bv_dom);
	  printf("\n");
	}
#endif
      if (!All_Diff_Tell_Value(i, x) || !All_Diff_Do_Propagation())
	{
#if 0
	  if (trace)
	    {
	      printf("cannot set [%3d] %2d/%-2d = %d dom: size:%d ", i, hol[i].l, hol[i].c, x, hol[i].ad_dom_size);
	      Display_Vector(hol[i].ad_bv_dom);
	      printf("\n");
	    }
#endif
	  All_Diff_Undo();

#if 0
	  if (hol[i].ad_dom_size == 1 && sol[i] != BV_First_Value(hol[i].ad_bv_dom))
	    printf("occurs: %d vs %d\n", sol[i], BV_First_Value(hol[i].ad_bv_dom));
#endif

	  sol[i] = -1;
	}
    }


#if 0
  for(i = 0; i < nb_hole; i++)
    if (hol[i].ad_dom_size == 1 && Random_Double() < 0.66)
      sol[i] = BV_First_Value(hol[i].ad_bv_dom);
#endif


}


static int
Reset_With_All_Diff(int n, AdData *p_ad)
{
  int i, l;

  static int save_sol[MAX_SIZE];
  memcpy(save_sol, sol, size * sizeof(int));


  if (trace)
    {
      printf("--- ENTRY -----------------------\n");
      Display_Solution_Color(p_ad0);
    }

  if (trace)
    {
      printf("BEFORE: ");
      for(i = 0; i < nb_hole; i++)
        printf(" %2d", sol[i]);
      printf("\n");
    }

  Partial_Repair_FF();

  if (trace)
    {
      int k = 0;
      printf("AFTER : ");
      for(i = 0; i < nb_hole; i++)
        {
          if (sol[i] < 0)
            k++;

          printf(" %2d", sol[i]);
        }
      printf("\n");
      printf("\nErrors: %3d  ratio: %.2lg\n", k, (double) k / nb_hole);
    }

  for(l = 0; l < order; l++)
    Random_Permut_Repair(sol + lin[l].beg_i, lin[l].nb_hol, lin[l].hole_val, 0);

#if 1
  int diff = 0;
  for(i = 0; i < nb_hole; i++)
    if (sol[i] != save_sol[i])
      diff++;

  diff /= 2;
  n -= diff;
  
#endif


  if (trace)
    {
      Display_Solution_Color(p_ad0);
      printf("--- EXIT -----------------------\n");
    }

  return n;
}

#endif	/* ALL_DIFF */



#define POOL_SIZE 8

  static int best_cost = 1<<30;
  static int best_iter = 0;
  static int pool_sol[POOL_SIZE][10000];
  static int pool_nb = 0;
  static int pool_cost[POOL_SIZE];
  static int count_pool = 0;
  static int incr = 3;

int
Reset(int n, AdData *p_ad)
{
#if 1
  if (trace == -1)
    trace = getenv("T") != NULL;
  if (trace)
    {
      printf("============================================== %d\n", p_ad->total_cost);
      Display_Solution_Color(p_ad);
      //  Check_Solution(p_ad);
    }
#endif


#if 0			   /* POOL UTILIZATION */

  if (reinit_pool)	/* another execution */
    {
      reinit_pool = 0;
      best_cost = 1<<30;
      best_iter = 0;
      pool_nb = 0;
      count_pool = 0;
      incr = 3;

    }

  if (p_ad->total_cost < best_cost)
    {
      if (trace)
	printf("BEST: %d\n", p_ad->total_cost);
      best_cost = p_ad->total_cost;
      best_iter = p_ad->nb_iter;
      incr = 3;
    }

  int z, imax = 0, max = 0;

  if (trace)
    {
      printf("Iter:%d - BEST:%d found at iter: %d  incr:%d   count_pool: %d\n", p_ad->nb_iter, best_cost, best_iter, incr, count_pool);
      for(z = 0; z < pool_nb; z++)
	printf(" POOL[%2d]: %d\n", z, pool_cost[z]);
    }

  int nb_best = 0;

  for(z = 0; z < pool_nb; z++)
    {
      if (pool_cost[z] == best_cost)
	nb_best++;
      
#if 0
#elif 1
      if (pool_cost[z] == p_ad->total_cost)
	{
	  int i, manath = 0;
	  for(i = 0; i < size; i++)
	    if (sol[i] != pool_sol[z][i])
	      manath++;
	  if (manath / 2 <  p_ad->total_cost - best_cost + 1)
	    goto dont_put;
	}
#elif 1
      if (pool_cost[z] == p_ad->total_cost)
	goto dont_put;
#else
      int i, manath = 0;
      for(i = 0; i < size; i++)
	if (sol[i] == pool_sol[z][i])
	  manath++;
      if (p_ad->total_cost >= pool_cost[z] && manath >= size * 0.8)
	goto dont_put;
#endif

      if (pool_cost[z] > max)
	{
	  imax = z;
	  max = pool_cost[z];
	}
    }
  if (pool_nb > 0 && p_ad->total_cost > (best_cost + max) / 2)
    goto dont_put;

  if (pool_nb < POOL_SIZE)
    imax = pool_nb++;

  if (trace)
    printf("ADD TO POOL AT [%d] in place of COST %d   NEW COST = %d\n", 
	   imax, pool_cost[imax], p_ad->total_cost);
  pool_cost[imax] = p_ad->total_cost;
  memcpy(pool_sol[imax], sol, size * sizeof(int));

 dont_put:
  if (count_pool-- == 0)
    {
      if (Random_Double() < 0.3)
	z = Random(pool_nb);
      else
	{
	  int k = Random(nb_best);
	  //	  printf("k:%d  nb_best:%d  size:%d\n", k, nb_best, pool_nb);
	  for(z = 0;; z++)
	    if (pool_cost[z] == best_cost && k-- == 0)
	      break;
	}
      count_pool = incr;
      incr = 10;
      //   if (incr > 100*order)	count_pool = incr = 3;
      if (p_ad->total_cost >= best_cost)
	{
	  if (trace)
	    {
	      printf("REUSE: POOL[%d] ==> %d   (next incr = %d)\n", z, pool_cost[z], incr);
	      Display_Solution_Color(p_ad);
	    }
	  memcpy(sol, pool_sol[z], size * sizeof(int));
	  p_ad->total_cost = pool_cost[z];
	  if (incr > 100*order)
	    {
	      incr = incr / 3;
	      if (trace)
		printf("diminish incr to %d\n", incr);
	    }
	  count_pool = incr;
#if 0
	  printf("Iter:%d - BEST:%d found at iter: %d\n", p_ad->nb_iter, best_cost, best_iter);
	  for(z = 0; z < pool_nb; z++)
	    printf("  POOL[%2d]: %d\n", z, pool_cost[z]);
	  printf("count_pool: %d   next incr: %d   n = %d   cost:%d\n\n", count_pool, incr, n, p_ad->total_cost);
#endif
	}
    }
#endif


  /*------------ END POOL --------*/


#ifdef ALL_DIFF
  n = Reset_With_All_Diff(n, p_ad);
#else
  if (nb_col_err < order / 4)
    n = Reset_Repair(n, p_ad);
  else
    n = Reset_Lines_Error(n, p_ad);
#endif

#if 0
  printf("***************** AFTER RESET LINES ERROR\n");
  Display_Solution_Color(p_ad);
  printf("****************** AFTERR -- cost: %d\n", Compute_Errors(NULL));
#endif


  int nh;
  int l, i, j, x, k;

  while(n > 0)
    {
      l = Random(order);
      nh = lin[l].nb_hol;
      if (nh <= 1)
	continue;

      for(k = 0; k < 3; k++)
	{
	  i = lin[l].beg_i + Random(nh);
	  do
	    j = lin[l].beg_i + Random(nh);
	  while (i == j);

	  n--;
	  p_ad->nb_swap++;

	  x = sol[i];
	  sol[i] = sol[j];
	  sol[j] = x;

#if UNMARK_AT_RESET == 1
	  Ad_Un_Mark(i);
	  Ad_Un_Mark(j);
#endif
	}
    }

  return -1;
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
  
  PLS_Load_Problem(p_ad->param_file); 
  p_ad->size = nb_hole;

  printf("Order: %d  nb hole orig:%d   nb hole: %d\n", order, nb_hole_orig, nb_hole);

  p_ad->first_best = 1;
				/* defaults */
  if (p_ad->prob_select_loc_min == -1)
    p_ad->prob_select_loc_min = (nb_hole * 100 / (order * order)) > 60 ? 10 : 80;

  if (p_ad->freeze_loc_min == -1)
    p_ad->freeze_loc_min = 1 ;

  if (p_ad->freeze_swap == -1)
    p_ad->freeze_swap = 0;

  if (p_ad->reset_limit == -1)
    p_ad->reset_limit = 5;

  if (p_ad->reset_percent == -1)
    p_ad->reset_percent = 10;

  if (p_ad->restart_limit == -1)
    p_ad->restart_limit = 1000000000;

  if (p_ad->restart_max == -1)
    p_ad->restart_max = 0;
}




/*
 *  DISPLAY_SOLUTION
 *
 *  Displays a solution.
 */

void
Display_Solution(AdData *p_ad)
{
  int *sol = p_ad->sol;
  int l, c, x;

  if (getenv("COLOR"))
    Display_Solution_Color(p_ad);
  else
    {
      if (order < 0)
	PLS_Load_Problem(p_ad->param_file);

      for(l = 0; l < order; l++)
	{
	  //      printf("line %2d:", l);
	  for(c = 0; c < order; c++)
	    {
	      x = lin[l].val[c];
	      if (x < 0)
		x = sol[-x - 1];
	      printf(" %3d", x);
	    }
	  printf("\n");
	}
    }
}





void
Display_Solution_Color(AdData *p_ad)
{
  int *sol = p_ad->sol;
  int l, c, i, x;
  BitVec bv_on_error;


  if (order < 0)
    PLS_Load_Problem(p_ad->param_file);

#define MARK_ERR_DOMAIN     (1 << 31)
#define MARK_ERR_ORTHER_VAR (1 << 30)

#define UNMARK(x)           ((x) &= ((1 << 30) - 1))

#define ANSI_NORMAL         "\033[0;30m" /* black */
#define ANSI_VAR_OK         "\033[1;32m" /* green */
#define ANSI_ERR_DOMAIN     "\033[0;41m" /* backgrnd = red */
#define ANSI_ERR_OTHER_VAR  "\033[1;31m" /* red */



  printf("colors: Fixed Value   %sVariable OK%s    %sErr Domain%s   %sErr dupl on col%s\n",
	 ANSI_VAR_OK, ANSI_NORMAL,
	 ANSI_ERR_DOMAIN, ANSI_NORMAL,
	 ANSI_ERR_OTHER_VAR, ANSI_NORMAL);

  
  BV_Empty(bv_on_error);

  for(c = 0; c < order; c++)
    {
      memset(count, 0, order * sizeof(int));
      for(l = 0; l < order; l++)
	{
	  x = lin[l].val[c];
	  if (x < 0)
	    {
	      i = -x - 1;
	      x = sol[i];
	      if (!BV_Has_Value(hol[i].bv_dom, x))
		{
		  BV_Set_Value(bv_on_error, x);
		  sol[i] |= MARK_ERR_DOMAIN;
		}
	    }

	  count[x]++;
	}

      for(x = 0; x < order; x++)
	if (count[x] > 1)
	  {
	    BV_Set_Value(bv_on_error, x);
	    for(l = 0; l < order; l++)
	      {
		i = -lin[l].val[c] - 1;
		if (i >= 0 && sol[i] == x)
		  sol[i] |= MARK_ERR_ORTHER_VAR;
	      }
	  }
    }

  printf("    ");
  for(c = 0; c < order; c++)
    printf(" %3d", c);
  printf("\n");
  printf("    ");
  for(c = 0; c < order; c++)
    printf("----");
  printf("\n");

  for(l = 0; l < order; l++)
    {
      printf("%2d | ", l);
      for(c = 0; c < order; c++)
	{
	  x = lin[l].val[c];
	  if (x < 0)
	    {
	      i = -x - 1;
	      x = sol[i];
	      if (x & MARK_ERR_DOMAIN)
		printf("%s", ANSI_ERR_DOMAIN);
	      else if (x & MARK_ERR_ORTHER_VAR)
		printf("%s", ANSI_ERR_OTHER_VAR);
	      else
		printf("%s", ANSI_VAR_OK);
	      
	      UNMARK(sol[i]);

	      x = sol[i];
	    }
	  printf("%3d%s ", x, ANSI_NORMAL);
	}
      printf("\n");
    }
  printf("on_error: %2d = ", BV_Cardinality(bv_on_error)); Display_Vector(bv_on_error); printf("\n");
}




/*
 *  CHECK_SOLUTION
 *
 *  Checks if the solution is valid.
 */

int
Check_Solution(AdData *p_ad)
{
  int *sol = p_ad->sol;
  int l, c, x;
  int r = 1;
  static int occ[MAX_ORDER];

  if (order < 0)
    PLS_Load_Problem(p_ad->param_file);

  for(l = 0; l < order; l++)
    {
      memset(occ, 0, order * sizeof(int));
      for(c = 0; c < order; c++)
	{
	  x = lin[l].val[c];
	  if (x < 0)
	    x = sol[-x - 1];
	  if (x < 0 || x >= order)
	    {
	      printf("ERROR at [%d][%d] invalid value %d (<0 or >= %d)\n", l, c, x, order);
	      r = 0;
	    }
	  occ[x]++;
	}
      for(x = 0; x < order; x++)
	if (occ[x] > 1)		/* use if (occ[x] != 1) to also display missing values */
	  {
	    printf("ERROR at line: %d value %d appears %d times\n", l, x, occ[x]);
	    r = 0;
	  }
    }

  for(c = 0; c < order; c++)
    {
      memset(occ, 0, order * sizeof(int));
      for(l = 0; l < order; l++)
	{
	  x = lin[l].val[c];
	  if (x < 0)
	    x = sol[-x - 1];
	  occ[x]++;
	}
      for(x = 0; x < order; x++)
	if (occ[x] > 1)		/* use if (occ[x] != 1) to also display missing values */
	  {
	    printf("ERROR at col.: %d value %d appears %d times\n", c, x, occ[x]);
	    r = 0;
	  }
    }

  return r;
}



int
Check_Solution_Line(AdData *p_ad)
{
  int *sol = p_ad->sol;
  int l, c, x;
  int r = 1;
  static int occ[MAX_ORDER];

  if (order < 0)
    PLS_Load_Problem(p_ad->param_file);

  for(l = 0; l < order; l++)
    {
      memset(occ, 0, order * sizeof(int));
      for(c = 0; c < order; c++)
	{
	  x = lin[l].val[c];
	  if (x < 0)
	    x = sol[-x - 1];
	  if (x < 0 || x >= order)
	    {
	      printf("ERROR at [%d][%d] invalid value %d (<0 or >= %d)\n", l, c, x, order);
	      r = 0;
	    }
	  occ[x]++;
	}
      for(x = 0; x < order; x++)
	if (occ[x] != 1)		/* use if (occ[x] != 1) to also display missing values */
	  {
	    printf("ERROR at line: %d value %d appears %d times\n", l, x, occ[x]);
	    r = 0;
	  }
    }
  return r;
}





void
Display_Vector(BitVec vec)
{
  int x;
  printf("{");

  BV_FOREACH(vec, x)
    {
      printf(" %2d", x);
    }

  printf("}");
}



/*----------------------------------------------------------------------------------------------------*/


#ifdef ALL_DIFF

static int timestamp = 0;

void
All_Diff_Init(void)
{
  timestamp++;
}

int
All_Diff_Tell_Domain(int i, BitVec bv_dom)
{
  int dom_size;

  BV_Intersect(bv_dom, bv_dom, hol[i].ad_bv_dom);
  dom_size = BV_Cardinality(bv_dom);

  if (dom_size == 0)
    return 0;

  if (dom_size == hol[i].ad_dom_size)
    return 2;		   /* nothing changed */

  if (hol[i].ad_save_timestamp < timestamp)
    {
      hol[i].ad_sos_bv_dom = hol[i].ad_bv_dom;
      hol[i].ad_sos_dom_size = hol[i].ad_dom_size;
      hol[i].ad_save_timestamp = timestamp;
    }
    
  hol[i].ad_bv_dom = bv_dom;
  hol[i].ad_dom_size = dom_size;
  hol[i].ad_propag_me_timestamp = timestamp;

  return 1;		   /* domain reduced */
}

int
All_Diff_Tell_Value(int i, int x)
{
  if (!BV_Has_Value(hol[i].ad_bv_dom, x))
    return 0;

  if (hol[i].ad_dom_size == 1)
    return 2;		   /* nothing changed */

  if (hol[i].ad_save_timestamp < timestamp)
    {
      hol[i].ad_sos_bv_dom = hol[i].ad_bv_dom;
      hol[i].ad_sos_dom_size = hol[i].ad_dom_size;
      hol[i].ad_save_timestamp = timestamp;
    }
    
  BV_Empty(hol[i].ad_bv_dom);
  BV_Set_Value(hol[i].ad_bv_dom, x);
  hol[i].ad_dom_size = 1;
  hol[i].ad_propag_me_timestamp = timestamp;

  return 1;		   /* domain reduced */
}

void
All_Diff_Undo()
{
  int i;

  for(i = 0; i < nb_hole; i++)
    if (hol[i].ad_save_timestamp == timestamp)
      {
	hol[i].ad_bv_dom = hol[i].ad_sos_bv_dom;
	hol[i].ad_dom_size = hol[i].ad_sos_dom_size;
	hol[i].ad_save_timestamp = 0;

	hol[i].ad_propag_me_timestamp = 0;
      }
}


int
All_Diff_Do_Propagation(void)
{
  int i, j, next_i;
  int l, c;
  int k, n;
  int ret;
  BitVec bv_dom_compl;
  int fix_point;

  do 
    {
      fix_point = 1;

#if 1
      /* pass 1: Value Consistency (VC) remove singletons (forward checking) */

      for(i = 0; i < nb_hole; i++)
	{
	  if (hol[i].ad_propag_me_timestamp < timestamp)
	    continue;

	  if (hol[i].ad_dom_size > 1)
	    continue;

	  hol[i].ad_propag_me_timestamp = 0;

	  l = hol[i].l;
	  c = hol[i].c;

	  BV_Complement(bv_dom_compl, hol[i].ad_bv_dom, order);

	  /* propagation of the All-Different on the same line */

	  next_i = lin[l].next_i;

	  for(j = lin[l].beg_i; j < next_i; j++)
	    {
	      if (j == i)
		continue;

	      ret = All_Diff_Tell_Domain(j, bv_dom_compl);

	      if (ret == 0)
		return 0;

	      if (ret == 1)
		fix_point = 0;
	    }

	  /* propagation of the All-Different on the same column */

	  n = col[c].nb_hol;

	  for(k = 0; k < n; k++)
	    {
	      j = col[c].hol[k]->i;
	      
	      if (j == i)
		continue;

	      ret = All_Diff_Tell_Domain(j, bv_dom_compl);

	      if (ret == 0)
		return 0;

	      if (ret == 1)
		fix_point = 0;
	    }
	}
#endif
#if 1
      /* This 'continue' is because the value consistency (VC) filtering 
       * is less costly than channel constraints 
       */
      if (!fix_point)
	continue;



      /* channeling constraints on lines:
	 for each line: if a missing value x only appears inside the domain of 1 variable of the line
	 this variable is set to x
      */


      //printf("--- LINE ----------------------\n");
      for(l = 0; l < order; l++)
	{
	  int next_i = lin[l].next_i;
	  BitVec bv_missing_val;
	  int x;

	  bv_missing_val = lin[l].bv_missing_val;
	  
	  BV_FOREACH(bv_missing_val, x)
	    {
	      int count = 0;
	      
	      for(i = lin[l].beg_i; i < next_i; i++)
		{
		  if (BV_Has_Value(hol[i].ad_bv_dom, x))
		    {
		      if (++count > 1)
			break;

		      j = i;
		    }
		}
#if 0
	      if (count == 0)	/* no room for value x */
		printf("cannot place value: %2d in line: %2d\n", x, l);
#endif
	      if (count == 0)	/* no room for value x */
		return 0;

#if 0
	      if (count == 1)
		{
		  printf("Value: %2d must go to line [%2d] %2d/%-2d  dom = ", x, j, l, hol[j].c);
		  Display_Vector(hol[j].ad_bv_dom);
		  printf("\n");
		}
#endif
	      

	      if (count == 1)
		{
		  ret = All_Diff_Tell_Value(j, x);

		  if (ret == 0)
		    return 0;

		  if (ret == 1) //printf("\tUPDATED\n"),
		    fix_point = 0;
		}
	    }
	}

      /* This 'continue' is because the value consistency (VC) filtering 
       * is less costly than channel constraints 
       */
      if (!fix_point)
	continue;

      /* channeling constraints on columns (see above) */

      for(c = 0; c < order; c++)
	{
	  n = col[c].nb_hol;
	  BitVec bv_missing_val;
	  int x;

	  bv_missing_val = col[c].bv_missing_val;
	  
	  BV_FOREACH(bv_missing_val, x)
	    {
	      int count = 0;
	      
	      for(k = 0; k < n; k++)
		{
		  i = col[c].hol[k]->i;

		  if (BV_Has_Value(hol[i].ad_bv_dom, x))
		    {
		      if (++count > 1)
			break;
		      j = i;
		    }
		}
#if 0
	      if (count == 0)	/* no room for value x */
		printf("cannot place value: %2d in col: %2d\n", x, l);
#endif

	      if (count == 0)	/* no room for value x */
		return 0;
#if 0
	      if (count == 1)
		printf("Value: %2d must go to col. [%2d] %2d/%-2d\n", x, j, hol[j].l, c);
#endif
	      if (count == 1)
		{
		  ret = All_Diff_Tell_Value(j, x);

		  if (ret == 0)
		    return 0;

		  if (ret == 1)
		    fix_point = 0;
		}
	    }
	}

#endif

    }
  while(!fix_point);

  return 1;
}


#endif /* ALL_DIFF */
