#ifndef _QCP_UTILS
#define _QCP_UTILS

#include "tools.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#ifndef No_Gcc_Warn_Unused_Result
# define No_Gcc_Warn_Unused_Result(t) if(t)
#endif


typedef int *	QCPVector;
typedef int **	QCPMatrix;


typedef struct {
  int row;
  int col;
} RowCol;

typedef struct {
  int		size;		/* size of the problem (always known) */
  int		**matrix;
  int		**constraints;
  int		**domains;
  int		**variables;
  RowCol	*coordinates;
  
} QCPInfo;



QCPMatrix QCP_Alloc_Matrix(int n)
{
  n++;
  QCPMatrix mat = malloc(n * sizeof(mat[0]));
  int i;

  if (mat == NULL)
    {
      fprintf(stderr, "%s:%d malloc failed\n", __FILE__, __LINE__);
      exit(1);
    }

  for(i = 0; i < n; i++)
    {
      mat[i] = malloc(n * sizeof(mat[0][0]));
      if (mat[i] == NULL)
	{
	  fprintf(stderr, "%s:%d malloc failed\n", __FILE__, __LINE__);
	  exit(1);
	}
    }
  return mat;
}

void QCP_Free_Matrix(QCPMatrix mat, int n)
{
  int i;
  for(i = 0; i < n; i++)
    free(mat[i]);

  free(mat);
}

#define QCP_Alloc_Vector(n)            malloc((n + 1) * sizeof(int))
#define QCP_Free_Vector(v)             free(v)
#define QCP_Copy_Vector(dst, src, n)   memcpy((dst), (src), (n) * sizeof(int))

void QCP_Free_Info(QCPInfo *q, int sizePb, int sizeMat)
{
  QCP_Free_Matrix(q->matrix, sizeMat);
  QCP_Free_Matrix(q->constraints, 2*sizeMat);
  QCP_Free_Matrix(q->domains, sizePb); 
  QCP_Free_Matrix(q->variables, sizeMat);
  QCP_Free_Vector(q->coordinates);  
}

void QCP_Read_Matrix(FILE *f, int n, QCPMatrix *pm)
{
  *pm = QCP_Alloc_Matrix(n);
  int i, j;

  for(i = 0; i < n; i++)
    for(j = 0; j < n; j++)
      if (fscanf(f, "%d", &((*pm)[i][j])) != 1)
	{
	  fprintf(stderr, "error while reading matrix at [%d][%d]\n", i, j);
	  exit(1);
	}
}


int* defDomains(int **matrix, int row, int col, int n)
{
  int *line = malloc(n * sizeof(int));
  int *domain;

  for (int i = 0; i < n; i++)
    line[i] = 0;

  int count = 0;
  for (int j = 0; j < n; j++)
    if (matrix[row][j] != -1 && line[matrix[row][j]] == 0)
      {
	line[matrix[row][j]] = 1;
	count++;
      }
  for (int i = 0; i < n; i++)
    if (matrix[i][col] != -1 && line[matrix[i][col]] == 0)
      {
	line[matrix[i][col]] = 1;
	count++;
      }

  domain = malloc((n + 1 - count) * sizeof(int));
  domain[0] = n - count;
  int index = 1;
  // printf("DEF[%d][%d] : ", row, col);
  for (int i = 0; i < n; i++)
    if (line[i] == 0)
      {
	// printf("%d ", i);
	domain[index] = i;
	index++;
      }

  free (line);
  //printf("\n");
  return domain;
}


/*
 *  Load a QCP problem
 *
 *  file_name: the file name of the QCP problem (can be a .dat or a .qap)
 *  qi: the ptr to the info structure (can be NULL)
 *      the matrix a and b are not allocated if the ptr != NULL at entry !
 *  
 */
void QCP_Load_Problem(char *file_name, QCPInfo *qi, int justVar, int *sizePb, int *sizeMat)
{
  int n;
  char c[5] = "";
  FILE *f;

  if ((f = fopen(file_name, "rt")) == NULL) 
    {
      perror(file_name);
      exit(1);
    }

  if (fscanf(f, "%s", c) != 1 || strcmp(c, "order"))
    {
      fprintf(stderr, "error while reading the size\n");
      exit(1);
    }

  if (fscanf(f, "%d", &n) != 1)
    {
      fprintf(stderr, "error while reading the size\n");
      exit(1);
    }

  if (justVar == 1)
    {
      int **matrix;
      QCP_Read_Matrix(f, n, &matrix);

      /* assigning variables index */
      int counter = 0;
      for (int row = 0; row < n; row++)
	for (int col = 0; col < n; col++)
	  if (matrix[row][col] == -1)
	    counter++;
      *sizePb = counter;
      QCP_Free_Matrix(matrix, n);
    }

  if (qi != NULL)		/* only need the size */
    {
      qi->size		= n;
      qi->constraints	= malloc(2*n * sizeof(int*));
      qi->variables	= malloc(n * sizeof(int*));

      for (int i = 0; i < 2*n; i++)
	{
	  qi->constraints[i] = malloc((n+1) * sizeof(int));
	  if (i < n)
	    qi->variables[i] = malloc(n * sizeof(int));

	  for (int j = 0; j < n; j++)
	    {
	      qi->constraints[i][j+1] = -1;
	      if (i < n)
		qi->variables[i][j] = -1;
	    }
	}
      
      QCP_Read_Matrix(f, n, &qi->matrix);

      /* assigning variables index */
      int counter = 0;
      for (int row = 0; row < n; row++)
	for (int col = 0; col < n; col++)
	  {
	    if (qi->matrix[row][col] == -1)
	      {
		qi->variables[row][col] = counter;
		counter++;
	      }
	  }

      qi->domains = malloc(counter * sizeof(int*));
      qi->coordinates = malloc(counter * sizeof(RowCol));
      *sizePb = counter;

      /* building constraints */     
      for (int row = 0; row < n; row++)
	{
	  int index = 1;
	  for (int col = 0; col < n; col++)
	    {
	      if (qi->matrix[row][col] == -1)
		{
		  qi->constraints[row][index] = qi->variables[row][col];
		  qi->coordinates[qi->variables[row][col]].row = row;
		  qi->coordinates[qi->variables[row][col]].col = col;
		  ++index;
		}
	    }
	  qi->constraints[row][0] = index-1;
	}
      for (int col = 0; col < n; col++)
	{
	  int index = 1;
	  for (int row = 0; row < n; row++)
	    {
	      if (qi->matrix[row][col] == -1)
		{
		  qi->constraints[col+n][index] = qi->variables[row][col];
		  ++index;
		}
	    }   
	  qi->constraints[col+n][0] = index-1;
	}
      
      /* determining domains for each variables */
      for (int col = 0; col < n; col++)
	for (int row = 0; row < n; row++)
	  {
	    if (qi->variables[row][col] != -1)
	      qi->domains[qi->variables[row][col]] = defDomains(qi->matrix, row, col, n);
	  }
    }

  *sizeMat = n;
  fclose(f);
}


void QCP_Display_Vector(QCPVector sol, int n)
{
  int i;
  for(i = 0; i < n; i++)
    printf("%d ", sol[i]);
  printf("\n");
}

void QCP_Display_Matrix(QCPMatrix mat, int n)
{
  int i, j;
  int max = 0;

  for (i = 0; i < n; i++)
    for (j = 0; j < n; j++)
      {
        if (mat[i][j] > max)
          max = mat[i][j];
      }

  int nb10 = 0;
  int max10 = 1;

  while(max >= max10)
    {
      nb10++;
      max10 *= 10;
    }

  for(i = 0; i < n; i++)
    {
      char *pref = "";
      for (j = 0; j < n; j++)
        {
          printf("%s%*d", pref, nb10, mat[i][j]);
          pref = " ";
        }
      printf("\n");
    }
}

#endif /* _QCP_UTILS */

