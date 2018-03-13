/*
 *  Adaptive search
 *
 *  Copyright (C) 2002-2012
 *
 *  quasigroup.c: Quasigroup Completion Problem (QCP)
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <math.h>
#include "ad_solver.h"

#define QCP_NO_MAIN
#include "quasigroup-utils.c"

AdData *p_ad0;

/*-----------*
 * Constants *
 *-----------*/

/*-------*
 * Types *
 *-------*/

/*------------------*
 * Global variables *
 *------------------*/

static int	size;		/* size of a side of the matrix */
static int	nbVar;		/* number of variables in p_ad->sol */
static QCPInfo	qcp_info;
static int	*sol;		/* copy of p_ad->sol */

static int	**constraints;
static int	**domains;
static int	**matrix;
static int	**variables;
static RowCol	*coordinates;

/*------------*
 * Prototypes *
 *------------*/

/*
 *  MODELING
 */


void sort(int **constraints, int **domains)
{
  int min;
  int ptr, tmp;

  // do for each line of the matrix
  for (int i = 0; i < size; i++)
    {
      // for each variable of the constraints[i]
      for (int j = 1; j < constraints[i][0]; j++)
	{
	  int index = j+1;
	  ptr = -1;
	  // look for the variable in constraints[i] with the smallest domain
	  min = domains[constraints[i][j]][0];
	  while (index <= constraints[i][0])
	    {
	      if (domains[constraints[i][index]][0] < min)
		{
		  min = domains[constraints[i][index]][0];
		  ptr = index;
		}
	      index++;
	    }

	  // place it at position j in constraints[i]
	  // (i.e. swap it with constraints[i][j])
	  if (ptr != -1 && ptr != j)
	    {
	      tmp = constraints[i][j];
	      constraints[i][j] = constraints[i][ptr];
	      constraints[i][ptr] = tmp;
	    }
	}
    }
}

int inDomain(int val, int *tab)
{
  for (int i = 1; i <= tab[0]; i++)
    if (val == tab[i])
      return 1;

  return 0;
}

/*
 *  SOLVE
 *
 *  Initializations needed for the resolution.
 */
void Solve(AdData *p_ad)
{
  if (constraints == NULL)		/* matrices not yet read */
    {
      QCP_Load_Problem(p_ad->param_file, &qcp_info, 0, &nbVar, &size);  
      constraints	= qcp_info.constraints;
      domains		= qcp_info.domains;
      matrix		= qcp_info.matrix;
      variables		= qcp_info.variables;
      coordinates	= qcp_info.coordinates;
      p_ad->size	= nbVar;

      sol = malloc(nbVar * sizeof(int));
      int *values = malloc(size * sizeof(int));

      //sort(constraints, domains);

#if defined DEBUG
      printf("\nMATRIX\n");
      QCP_Display_Matrix(matrix, size);
      
      printf("\nVARIABLES\n");
      QCP_Display_Matrix(variables, size);
      
      printf("\nCONSTRAINTS\n");
      for (int i = 0; i < 2*size; i++)
      	{
      	  if (i < size)
      	    printf("row %d : ", i);
      	  else
      	    printf("column %d : ", i-size);
	  
      	  for (int j = 1; j <= constraints[i][0]; j++)
	    printf("%d ", constraints[i][j]);
      	  printf("\n");
      	}
      
      printf("\nDOMAINS\n");
      for (int i = 0; i < nbVar; i++)
      	{
      	  printf("Var %d (%d) : ", i, domains[i][0]);
      	  for (int j = 1; j <= domains[i][0]; j++)
      	    printf("%d ", domains[i][j]);
      	  printf("\n");
      	}
      printf("\n");
#endif /* !DEBUG */

      for (int row = 0; row < size; row++)
	{
	  for (int i = 0; i < size; i++)
	    values[i] = 0;
	    	    
	  for (int col = 0; col < size; col++)
	    if (matrix[row][col] != -1)
	      values[matrix[row][col]] = 1;
	
	  for (int index = 1; index <= constraints[row][0]; index++)
	    {
	      for (int i = index-1; i < size; i++)
		{
		  if (values[i] == 0)
		    {
		      int var = constraints[row][index];
		      /* if (inDomain(i, domains[var]) == 1) */
		      /* 	{ */
		      /* 	  p_ad->sol[var] = i; */
		      /* 	  values[i] = 1; */
		      /* 	  break; */
		      /* 	} */
		      p_ad->sol[var] = i;
		      values[i] = 1;
		      break;
		    }
		}
	    }
	}

      free (values);
    }  
  
  for (int i = 0; i < nbVar; i++)
    sol[i] = p_ad->sol[i];

#if defined DEBUG
  printf("INITIAL VALUES\n");
  for (int i = 0; i < nbVar; i++)
    printf("%d ", p_ad->sol[i]);
  printf("\n");
#endif

  Ad_Solve(p_ad);
  p_ad0 = p_ad;

  // copy of matrix and variables before deleting qcp_info
  // we need them for solution checking
  matrix = QCP_Alloc_Matrix(size);
  variables = QCP_Alloc_Matrix(size);
  for (int i = 0; i < size; i++)
    for (int j = 0; j < size; j++)
      {
	matrix[i][j] = qcp_info.matrix[i][j]; 
	variables[i][j] = qcp_info.variables[i][j];
      }  

  QCP_Free_Info(&qcp_info, nbVar, size);
}


/*
 *  COST_OF_SOLUTION
 *
 *  Returns the total cost of the current solution.
 *  Also computes errors on constraints for subsequent calls to
 *  Cost_On_Variable, Cost_If_Swap and Executed_Swap.
 */
int Cost_Of_Solution(int should_be_recorded)
{
  int occurences = 0;
  int n = size;
  int line[n];

  /* number of doubloons in rows */
  for (int row = 0; row < n; row++)
    {
      for (int i = 0; i < n; i++)
	line[i] = 0;

      for (int col = 0; col < n; col++)
	{
	  if (matrix[row][col] != -1)
	    {
	      if (line[matrix[row][col]] == 0)
		line[matrix[row][col]] = 1;
	      else
		occurences++;
	    }
	  else
	    {
	      if (line[sol[variables[row][col]]] == 0)
		line[sol[variables[row][col]]] = 1;
	      else
		occurences++;
	    }
	}
    }      
  /* number of doubloons in columns */
  for (int col = 0; col < n; col++)
    {
      for (int i = 0; i < n; i++)
	line[i] = 0;

      for (int row = 0; row < n; row++)
	{
	  if (matrix[row][col] != -1)
	    {
	      if (line[matrix[row][col]] == 0)
		line[matrix[row][col]] = 1;
	      else
		occurences++;
	    }
	  else
	    {
	      if (line[sol[variables[row][col]]] == 0)
		line[sol[variables[row][col]]] = 1;
	      else
		occurences++;
	    }
	}
    }      
  
  return occurences;
}


/*
 *  COST_IF_SWAP
 *
 *  Evaluates the new total cost for a swap.
 *  Returns INT_MAX if:  
 *	- variables x and y are neither on the same row nor the same column.
 *	- value of x is not in the domain of y and vice versa.
 */
int Cost_If_Swap(int current_cost, int y, int x)
{
  if (y == x || sol[y] == sol[x])
    return current_cost;

  int rowX = coordinates[x].row;
  int colX = coordinates[x].col;

  int rowY = coordinates[y].row;
  int colY = coordinates[y].col;

  int n = size;

  //printf("COST IF SWAP %d (%d) and %d (%d) : ", x, sol[x], y, sol[y]);

  if (!inDomain(sol[y], domains[x]))
    {
      /* printf("MAX y not in Dom(x)\n"); */
      return INT_MAX;
    }
  else
    {
      if (!inDomain(sol[x], domains[y]))
	{
	  /* printf("MAX x not in Dom(y)\n"); */
	  return INT_MAX;
	}
    }
  
  // Does x and y are on the same row?
  if (rowX == rowY)
    {
      int costColX = 0;
      int costColY = 0;
      int futureCostColX = 0;
      int futureCostColY = 0;

      int lineX[n];
      int lineY[n];

      for (int i = 0; i < n; i++)
	{
	  lineX[i] = 0;
	  lineY[i] = 0;
	}

      // Cost of column for X and Y before swap (i.e., current state)
      for (int row = 0; row < n; row++)
	{
	  if (matrix[row][colX] != -1)
	    {
	      if (lineX[matrix[row][colX]] == 0)
		lineX[matrix[row][colX]] = 1;
	      else
		costColX++;
	    }
	  else
	    {
	      if (lineX[sol[variables[row][colX]]] == 0)
		lineX[sol[variables[row][colX]]] = 1;
	      else
		costColX++;
	    }

	  if (matrix[row][colY] != -1)
	    {
	      if (lineY[matrix[row][colY]]  == 0)
		lineY[matrix[row][colY]] = 1;
	      else
		costColY++;
	    }
	  else
	    {
	      if (lineY[sol[variables[row][colY]]] == 0)
		lineY[sol[variables[row][colY]]] = 1;
	      else
		costColY++;
	    }
	}

      for (int i = 0; i < n; i++)
	{
	  lineX[i] = 0;
	  lineY[i] = 0;
	}

      // Cost of these columns after swapping X and Y
      for (int row = 0; row < n; row++)
	{
	  int col;
	  if (row == rowX)
	    col = colY;
	  else
	    col = colX;
	  
	  if (matrix[row][col] != -1)
	    {
	      if (lineX[matrix[row][col]] == 0)
		lineX[matrix[row][col]] = 1;
	      else
		futureCostColX++;
	    }
	  else
	    {
	      if (lineX[sol[variables[row][col]]] == 0)
		lineX[sol[variables[row][col]]] = 1;
	      else
		futureCostColX++;
	    }
	  
	  if (row == rowY)
	    col = colX;
	  else
	    col = colY;
	  
	  if (matrix[row][col] != -1)
	    {
	      if (lineY[matrix[row][col]] == 0)
		lineY[matrix[row][col]] = 1;
	      else
		futureCostColY++;
	    }
	  else
	    {
	      if (lineY[sol[variables[row][col]]] == 0)
		lineY[sol[variables[row][col]]] = 1;
	      else
		futureCostColY++;
	    }
	}
#if DEBUG
       printf("cost if swap row %d, (c:%d, fx:%d, x:%d, fy:%d, y:%d)\n",
       	      current_cost + (futureCostColX - costColX) + (futureCostColY - costColY), current_cost, futureCostColX, costColX, futureCostColY, costColY);
#endif
      return (current_cost + (futureCostColX - costColX) + (futureCostColY - costColY));
    }
  // X and Y are not on the same row. Same column?
  else
    {
      if (colX == colY)
	{
	  int costRowX = 0;
	  int costRowY = 0;
	  int futureCostRowX = 0;
	  int futureCostRowY = 0;
	  
	  int lineX[n];
	  int lineY[n];

	  for (int i = 0; i < n; i++)
	    {
	      lineX[i] = 0;
	      lineY[i] = 0;
	    }
	  
	  // Cost of row for X and Y before swap (i.e., current state)
	  for (int col = 0; col < n; col++)
	    {
	      if (matrix[rowX][col] != -1)
		{
		  if (lineX[matrix[rowX][col]] == 0)
		    lineX[matrix[rowX][col]] = 1;
		  else
		    costRowX++;
		}
	      else
		{
		  if (lineX[sol[variables[rowX][col]]] ==0)
		    lineX[sol[variables[rowX][col]]] = 1;
		  else
		    costRowX++;
		}
		  
	      if (matrix[rowY][col] != -1)
		{
		  if (lineY[matrix[rowY][col]] == 0)
		    lineY[matrix[rowY][col]] = 1;
		  else		  
		    costRowY++;
		}
	      else
		{
		  if (lineY[sol[variables[rowY][col]]] == 0)
		    lineY[sol[variables[rowY][col]]] = 1;
		  else
		    costRowY++;
		}
	    }

	  for (int i = 0; i < n; i++)
	    {
	      lineX[i] = 0;
	      lineY[i] = 0;
	    }
	  
	  // Cost of these rows after swapping X and Y
	  for (int col = 0; col < n; col++)
	    {
	      int row;
	      if (col == colX)
		row = rowY;
	      else
		row = rowX;
	      
	      if (matrix[row][col] != -1)
		{
		  if (lineX[matrix[row][col]] == 0)
		    lineX[matrix[row][col]] = 1;
		  else
		    futureCostRowX++;
		}
	      else
		{
		  if (lineX[sol[variables[row][col]]] == 0)
		    lineX[sol[variables[row][col]]] = 1;
		  else
		    futureCostRowX++;
		}  
	      
	      if (col == colY)
		row = rowX;
	      else
		row = rowY;
	      
	      if (matrix[row][col] != -1)
		{
		  if (lineY[matrix[row][col]] == 0)
		    lineY[matrix[row][col]] = 1;
		  else
		    futureCostRowY++;
		}
	      else
		{
		  if (lineY[sol[variables[row][col]]] == 0)
		    lineY[sol[variables[row][col]]] = 1;
		  else
		    futureCostRowY++;
		}
	    }
	  
#ifdef DEBUG
	  printf("cost if swap column %d, (c:%d, fx:%d, x:%d, fy:%d, y:%d)\n",
	  	 current_cost + (futureCostRowX - costRowX) + (futureCostRowY - costRowY), current_cost, futureCostRowX, costRowX, futureCostRowY, costRowY);
#endif
	  return (current_cost + (futureCostRowX - costRowX) + (futureCostRowY - costRowY));
	}
      // X and Y are neither on the same row nor the same column: we cannot swap them!
      else
	{
	  /* printf("MAX not same row/col\n"); */
	  return INT_MAX;
	}
    }  
}


/*
 *  COST_ON_VARIABLE
 *
 *  Evaluates the error on a variable.
 */
int Cost_On_Variable(int k)
{
  int rowK = coordinates[k].row;
  int colK = coordinates[k].col;

  int errors = 0;
  //int line[size];

  // same value of k on its column
  for (int row = 0; row < size; row++)
    {
      if (row == rowK)
	continue;
      if (matrix[row][colK] != -1)
	{
	  if (matrix[row][colK] == sol[k])
	    errors++;
	}
      else
	{
	  if (sol[variables[row][colK]] == sol[k])
	    errors++;
	}
    }

  // same value of k on its row
  for (int col = 0; col < size; col++)
    {
      if (col == colK)
	continue;
      if (matrix[rowK][col] != -1)
  	{
  	  if (matrix[rowK][col] == sol[k])
  	    errors++;
  	}
      else
  	{
  	  if (sol[variables[rowK][col]] == sol[k])
	    errors++;
  	}
    }

  /* // errors on column of k */
  /* for (int row = 0; row < size; row++) */
  /*   { */
  /*     for (int i = 0; i < size; i++) */
  /* 	line[i] = 0; */

  /*     if (matrix[row][colK] != -1) */
  /* 	{ */
  /* 	  if (line[matrix[row][colK]] == 0) */
  /* 	    line[matrix[row][colK]] = 1; */
  /* 	  else */
  /* 	    errors++; */
  /* 	} */
  /*     else */
  /* 	{ */
  /* 	  if (line[sol[k]] == 0) */
  /* 	    line[sol[k]] = 1; */
  /* 	  else */
  /* 	    errors++; */
  /* 	} */
  /*   } */

  /* // errors on row of k */
  /* for (int col = 0; col < size; col++) */
  /*   { */
  /*     for (int i = 0; i < size; i++) */
  /* 	line[i] = 0; */

  /*     if (matrix[rowK][col] != -1) */
  /* 	{ */
  /* 	  if (line[matrix[rowK][col]] == 0) */
  /* 	    line[matrix[rowK][col]] = 1; */
  /* 	  else */
  /* 	    errors++; */
  /* 	} */
  /*     else */
  /* 	{ */
  /* 	  if (line[sol[k]] == 0) */
  /* 	    line[sol[k]] = 1; */
  /* 	  else */
  /* 	    errors++; */
  /* 	} */
  /*   } */

  return errors;
}


/*
 *  EXECUTED_SWAP
 *
 *  Records a swap.
 */
void Executed_Swap(int x, int y)
{
  printf("swapping var %d (%d) and %d (%d)\n", x, sol[x], y, sol[y]);
  Display_Solution(p_ad0);
#if 0
  int tmp = sol[x];
  sol[x] = sol[y];
  sol[y] = tmp;
  //printf("swapping var %d (%d) and %d (%d)\n", x, sol[x], y, sol[y]);
#endif
}


/*
 *  RESET
 *
 * Performs a reset (returns the new cost or -1 if unknown or some other data are not updated)
 *
 */
int Reset(int n, AdData *p_ad)
{
  int randRow;
  int randCol;

  int randX, randY;
  int tmp;

  for (int i = 0; i < (int)ceil((float)n / 2); i++)
    {
      randRow = Random(size);
      randX = Random(constraints[randRow][0]);
      randY = Random(constraints[randRow][0]);
      
      tmp = p_ad->sol[randX];
      p_ad->sol[randX] = p_ad->sol[randY];
      p_ad->sol[randY] = tmp;
      
      randCol = Random(size);
      randX = Random(constraints[randCol+n][0]);
      randY = Random(constraints[randCol+n][0]);
      
      tmp = p_ad->sol[randX];
      p_ad->sol[randX] = p_ad->sol[randY];
      p_ad->sol[randY] = tmp;
    }

  return -1;
}


int param_needed = -1;		/* overwrite var of main.c */

/*
 *  INIT_PARAMETERS
 *
 *  Initialization function.
 */
void Init_Parameters(AdData *p_ad)
{
  int dummy;
  int sizePb;
  QCP_Load_Problem(p_ad->param_file, NULL, 1, &sizePb, &dummy);
  p_ad->size = sizePb;

  /* defaults */
  if (p_ad->prob_select_loc_min == -1)
    p_ad->prob_select_loc_min = 50;

  if (p_ad->freeze_loc_min == -1)
    p_ad->freeze_loc_min = p_ad->size;

  if (p_ad->freeze_swap == -1)
    p_ad->freeze_swap = 0;

  if (p_ad->reset_limit == -1)
    p_ad->reset_limit = 1;

  if (p_ad->reset_percent == -1)
    p_ad->reset_percent = 4;

  if (p_ad->restart_limit == -1)
    p_ad->restart_limit = 1000000000;

  if (p_ad->restart_max == -1)
    p_ad->restart_max = 0;
}


/*
 *  CHECK_SOLUTION
 *
 *  Checks if the solution is valid.
 */
int Check_Solution(AdData *p_ad)
{
  int *sol = p_ad->sol;
  int n = size;
  int line[n];

  for (int row = 0; row < n; row++)
    {
      for (int i = 0; i < n; i++)
	line[i] = 0;
      
      for (int col = 0; col < n; col++)
	{
	  if (matrix[row][col] != -1)
	    {
	      if (line[matrix[row][col]] == 0)
		line[matrix[row][col]] = 1;
	      else
		{
		  printf("ERROR at (%d, %d): doubloon row mat\n", row, col);
		  QCP_Free_Matrix(matrix, size);
		  QCP_Free_Matrix(variables, size);
		  free (sol);  
		  return 0;
		}
	    }
	  else
	    {
	      if (line[sol[variables[row][col]]] == 0)
		line[sol[variables[row][col]]] = 1;
	      else
		{
		  printf("ERROR at (%d, %d): doubloon row var\n", row, col);
		  QCP_Free_Matrix(matrix, size);
		  QCP_Free_Matrix(variables, size);
		  free (sol);  
		  return 0;
		}
	    }  
	}
    }

  for (int col = 0; col < n; col++)
    {
      for (int i = 0; i < n; i++)
	line[i] = 0;
      
      for (int row = 0; row < n; row++)
	{
	  if (matrix[row][col] != -1)
	    {
	      if (line[matrix[row][col]] == 0)
		line[matrix[row][col]] = 1;
	      else
		{
		  printf("ERROR at (%d, %d): doubloon col mat\n", row, col);
		  QCP_Free_Matrix(matrix, size);
		  QCP_Free_Matrix(variables, size);
		  free (sol);  
		  return 0;
		}
	    }
	  else
	    {
	      if (line[sol[variables[row][col]]] == 0)
		line[sol[variables[row][col]]] = 1;
	      else
		{
		  printf("ERROR at (%d, %d): doubloon col var\n", row, col);
		  QCP_Free_Matrix(matrix, size);
		  QCP_Free_Matrix(variables, size);
		  free (sol);  
		  return 0;
		}
	    }  
	}
    }
  
  QCP_Free_Matrix(matrix, size);
  QCP_Free_Matrix(variables, size);
  free (sol);  
  return 1;
}

/*
 *  DISPLAY_SOLUTION
 *
 *  Displays a solution.
 */
void Display_Solution(AdData *p_ad)
{
  for(int row = 0; row < size; ++row)
    {
      for (int col = 0; col < size; ++col)
	{
	  if (matrix[row][col] != -1)
	    {
	      printf("  %3d ", matrix[row][col]);
	    }
	  else
	    {
	      printf(" [%3d] ", p_ad->sol[variables[row][col]]);
	    }
	}
      printf("\n");
    }
  printf("\n");
}
