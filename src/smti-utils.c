#ifndef _SMTI_UTILS
#define _SMTI_UTILS

#include "tools.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <ctype.h>

#ifndef No_Gcc_Warn_Unused_Result
#define No_Gcc_Warn_Unused_Result(t) if(t)
#endif


typedef int32_t SMPInt;



#define SMP_MAXINT    ((SMPInt)(0xFFFF))

typedef SMPInt *SMPVector;
typedef SMPInt **SMPMatrix;


typedef struct {
  //  char file_name[128];

  int size;			/* size of the problem */
  int p1;
  int p2;
  SMPMatrix pref_m;		/* men preference matrix */
  SMPMatrix pref_w;		/* women preference matrix */
} SMPInfo;



#define Pack(person, rank)  (((rank) << 16) | (person))
#define Unpack(z, person, rank)  do { (rank) = (z) >> 16; (person) = (z) & 0xFFFF; } while(0)


SMPVector
SMP_Alloc_Vector(int size)
{
  SMPVector vec = malloc((size + 1) * sizeof(*vec)); /* size+1 for final -1 */
  if (vec == NULL)
    {
      fprintf(stderr, "%s:%d malloc failed\n", __FILE__, __LINE__);
      exit(1);
    }

  return vec;
}



#define SMP_Free_Vector(v)  free(v)


#define SMP_Copy_Vector(dst, src, size)   memcpy((dst), (src), (size + 1) * sizeof(SMPInt))


SMPMatrix
SMP_Alloc_Matrix(int size)
{
  int i;
  SMPMatrix mat = malloc(size * sizeof(*mat));

  if (mat == NULL)
    {
      fprintf(stderr, "%s:%d malloc failed\n", __FILE__, __LINE__);
      exit(1);
    }

  for(i = 0; i < size; i++)
    {
      mat[i] = SMP_Alloc_Vector(size);
    }

  return mat;
}

void
SMP_Free_Matrix(SMPMatrix mat, int size)
{
  int i;
  for(i = 0; i < size; i++)
    free(mat[i]);

  free(mat);
}


#define RD_ERROR         ((1 << 30) | 0)
#define RD_END_OF_FILE   ((1 << 30) | 1)
#define RD_NEW_LINE      ((1 << 30) | 2)

int 
Read_Integer(FILE *f, int ignore_new_line)
{
  int c, x;
  do
    {
      c = getc(f);
      if (c == EOF)
	return RD_END_OF_FILE;

      if (c == '\n' && !ignore_new_line)
	return RD_NEW_LINE;
    }
  while(isspace(c));
  
  ungetc(c, f);
  if (fscanf(f, "%d", &x) != 1)
    x = RD_ERROR;

  return x; 
}


void
SMP_Read_Matrix(FILE *f, int size, SMPMatrix *pm, int format_is_dat)
{
  int m, w, k;

  if (*pm == NULL)
    *pm = SMP_Alloc_Matrix(size);

  for(m = 0; m < size; m++)
    {
      int rank = -1;
      if (format_is_dat && (w = Read_Integer(f, 1)) != m + 1)
	{
	  fprintf(stderr, "error while reading matrix at [%d] <first value to ignore>\n", m);
	  exit(1);
	}

      for(k = 0; k < size; k++)
	{
	  w = Read_Integer(f, m == 0 && k == 0); /* only ignore new line at beginning of matrix */

	  if (w == RD_END_OF_FILE || w == RD_NEW_LINE)
	    break;

	  if (w == RD_ERROR)
	    {
	      fprintf(stderr, "error while reading matrix at [%d][%d]\n", m, k);
	      exit(1);
	    }

	  if (w == 0) /* does not occur with our generator but we accept 0 as a removed value */
	    {
	      k--;
	      continue;
	    }

	  if (w < 0)
	    w = -w;
	  else
	    rank++;

	  w--;			/* 1-based */
	  (*pm)[m][k] = Pack(w, rank);
	}

      (*pm)[m][k] = -1;		/* final -1 */
    }
#if 0
  void SMP_Write_Matrix(FILE *f, int size, SMPMatrix pm, int format_is_dat);
  printf("-- matrix ---\n");
  SMP_Write_Matrix(stdout, size, *pm, format_is_dat);
  printf("-------------\n");
#endif

}




/*
 *  Generate a Permutation
 *
 *  Generate a vector of size elements with a random permutation of 0..size-1
 *  Use the Durstenfeld implementation of Fisher-Yates shuffle:
 */

void
SMP_Random_Vector(SMPVector vec, int size)
{
  int i, j;

  vec[0] = 0;
  for(i = 1; i < size; i++)
    {
      j = Random(i + 1);
      vec[i] = vec[j];
      vec[j] = i;
    }
}




SMPMatrix
SMP_Random_Matrix(int size)
{
  int i;
  SMPMatrix mat = SMP_Alloc_Matrix(size);

  for(i = 0; i < size; i++)
    SMP_Random_Vector(mat[i], size);

  return mat;
}




void
SMP_Write_Matrix(FILE *f, int size, SMPMatrix pm, int format_is_dat)
{
  int m, w, k, z;

  for(m = 0; m < size; m++)
    {
      int prev_rank = -1;		/* impossible value */
      int rank;

      if (format_is_dat)
	fprintf(f, "%d ", (m + 1));

      for(k = 0; (z = pm[m][k]) >= 0; k++)
	{
	  if (k)
	    fprintf(f, " ");

	  Unpack(z, w, rank);
	  w++;			/* 1-based values */
	  if (rank == prev_rank)
	    w = -w;
	  else
	    prev_rank = rank;

	  fprintf(f, "%d", w);
	}
      fprintf(f, "\n");
    }
}




char *
Get_Suffix(char *file_name)
{
  char *p = strrchr(file_name, '.');
  char *q = strrchr(file_name, '/');
  if (q == NULL)
    q = strrchr(file_name, '\\');

  if (p == NULL || p < q)
    p = file_name + strlen(file_name);

  return p;
}


int
Has_Dat_Suffix(char *file_name)
{
  return strcasecmp(Get_Suffix(file_name), ".dat") == 0;
}




int
Has_Smp_Suffix(char *file_name)
{
  return strcasecmp(Get_Suffix(file_name), ".smp") == 0;
}




/*
 *  Load a SMP problem
 *
 *  file_name: the file name of the SMP problem (can be a .dat or a .smp)
 *  qi: the ptr to the info structure (can be NULL)
 *      the matrix a and b are not allocated if the ptr != NULL at entry !
 *
 *  Returns the size of the problem
 */
int
SMP_Load_Problem(char *file_name, SMPInfo *p_smp_info)
{
  int size, p1, p2;
  FILE *f;
  int format_is_dat = Has_Dat_Suffix(file_name);

  if ((f = fopen(file_name, "rt")) == NULL) {
    perror(file_name);
    exit(1);
  }

  size = Read_Integer(f, 1);
  if (size == RD_END_OF_FILE || size == RD_ERROR)
    {
      fprintf(stderr, "error while reading the size\n");
      exit(1);
    }

  if (p_smp_info == NULL)	/* only need the size */
    return size;

  p1 = Read_Integer(f, 0);
  if (p1 == RD_END_OF_FILE || p1 == RD_ERROR)
    {
      fprintf(stderr, "error while reading p1 (percentage)\n");
      exit(1);
    }
  if (p1 == RD_NEW_LINE)
    {
      p1 = p2 = -1;			/* unknown */
    }
  else
    {
      p2 = Read_Integer(f, 0);
      if (p2 == RD_END_OF_FILE || p2 == RD_ERROR)
	{
	  fprintf(stderr, "error while reading p2 (percentage)\n");
	  exit(1);
	}
      if (p2 == RD_NEW_LINE)
	{
	  p2 = -1;			/* unknown */
	}
    }


  p_smp_info->size = size;
  p_smp_info->p1 = p1;
  p_smp_info->p2 = p2;

  SMP_Read_Matrix(f, size, &p_smp_info->pref_m, format_is_dat);
  SMP_Read_Matrix(f, size, &p_smp_info->pref_w, format_is_dat);

  fclose(f);
  
  return size;
}



/*
 *  Write a SMP problem
 *
 *  file_name: the file name of the SMP problem (a .smp)
 */
void
SMP_Write_Problem(char *file_name, SMPInfo *p_smp_info)
{
  int size = p_smp_info->size;
  int p1 = p_smp_info->p1;
  int p2 = p_smp_info->p2;
  FILE *f;
  int format_is_dat = Has_Dat_Suffix(file_name);

  if ((f = fopen(file_name, "wt")) == NULL) {
    perror(file_name);
    exit(1);
  }

  fprintf(f, "%d", size);
  if (p1 >= 0 || p2 >= 0)
    fprintf(f, " %d %d", p1, p2);
  fprintf(f, "\n\n");

  SMP_Write_Matrix(f, size, p_smp_info->pref_m, format_is_dat);
  fprintf(f, "\n");
  SMP_Write_Matrix(f, size, p_smp_info->pref_w, format_is_dat);

  fclose(f);
}



/*
 *  Generate an SMTI problem
 *
 *  size: the size of the problem
 *  p1 : probability as percentage of incompleteness (SMI)
 *  p2 : probability as percentage of ties (SMT)
 */
void
SMP_Generate_Problem(int size, int p1, int p2, SMPInfo *p_smp_info)
{
  SMPMatrix pref_m, pref_w;
  int m, w, k, j;

  p_smp_info->size = size;
  p_smp_info->p1 = p1;
  p_smp_info->p2 = p2;

  pref_m = p_smp_info->pref_m = SMP_Random_Matrix(size);
  pref_w = p_smp_info->pref_w = SMP_Random_Matrix(size);


  /* create some holes with prob p1 */

  if (p1 > 0) 
    {
      for(m = 0; m < size; m++)
	{
	  for(k = 0; k < size; k++)
	    {
	      w = pref_m[m][k];
	      if (Random(100) < (unsigned) p1) /* remove a man pref */
		{
		  pref_m[m][k] = -1;
		  for(j = 0; j < size; j++)
		    if (pref_w[w][j] == m)
		      {
			pref_w[w][j] = -1; /* removing corresponding woman pref */
			break;
		      }
		}
	    }
	}
    }

  /* fix the 2 matrices: trim vectors removing -1 and add final -1 */

  for(m = 0; m < size; m++)
    {
      int dst_m;
      int dst_w;
      if (p1 > 0)
	{
	  dst_m = dst_w = 0;
	  for(k = 0; k < size; k++)
	    {
	      w = pref_m[m][k];	/* vector in man */
	      if (w >= 0)
		pref_m[m][dst_m++] = w;
	  
	      w = pref_w[m][k];	/* vector in woman */
	      if (w >= 0)
		pref_w[m][dst_w++] = w;
	    }
	}
      else
	dst_m = dst_w = size;

      pref_m[m][dst_m] = -1; /* final -1 */
      pref_w[m][dst_w] = -1; /* final -1 */
    }


  /* add ties */

  for(m = 0; m < size; m++)
    {
      int rank_m = -1;
      int rank_w = -1;
      for(k = 0; k < size; k++)
	{
	  if (k == 0 || Random(100) >= (unsigned) p2) /* not a tie: incr rank */
	    rank_m++;
	  pref_m[m][k] = Pack(pref_m[m][k], rank_m);

	  if (k == 0 || Random(100) >= (unsigned) p2) /* not a tie: incr rank */
	    rank_w++;
	  pref_w[m][k] = Pack(pref_w[m][k], rank_w);
	}
    }
}



void
SMP_Display_Vector(SMPVector vec, int size)
{
  int i;
  for(i = 0; i < size; i++)
    printf("%d ", vec[i]);
  printf("\n");
}


void
SMP_Display_Matrix(SMPMatrix mat, int size, int with_index)
{
  int m, w, k, z;
  int fmt_len = 0;
  char buff[32];
  int rank, next_rank;
  int longest_line = 0;
  
  for (m = 0; m < size; m++)
    {
      for (k = 0; (z = mat[m][k]) >= 0; k++)
	{
	  Unpack(z, w, rank);
	  w++;			/* 1-based values */
	  sprintf(buff, "%d", w);
	  int len = strlen(buff);
	  if (len > fmt_len)
	    fmt_len = len;
	}
      if (k >= longest_line)
	longest_line = k;
    }


  if (with_index)
    {
      printf("%*s", fmt_len, "");
      for (k = 0; k < longest_line; k++)
        {
          printf("  %*d", fmt_len, k);
        }
      printf("\n");
      printf("%*s ", fmt_len, "");
      for (k = 0; k < longest_line; k++)
        {
          printf("%*s", (fmt_len + 1), ".");
        }
      printf("\n");
    }


  for(m = 0; m < size; m++)
    {
      if (with_index)
	printf("%*d:", fmt_len, m);
      

      int in_tie = 0;
      for (k = 0; (z = mat[m][k]) >= 0; k++)
        {
	  Unpack(z, w, rank);
	  w++;			/* 1-based values */

	  Unpack(mat[m][k+1], z, next_rank); /* works since -1 at end */
	  if (!in_tie && rank == next_rank)	      /* begin a tie */
	    {
	      in_tie = 1;
	      printf("(");
	    }
	  else
	    printf(" ");


	  printf("%*d", fmt_len, w);

	  if (in_tie && rank != next_rank)
	    {
	      in_tie = 0;
	      printf(")");
	    }
	  else
	    printf(" ");
        }
      printf("\n");
    }
}




void
SMP_Display_Problem(SMPInfo *p_smp_info, int with_index)
{
  int size = p_smp_info->size;
  int p1 =  p_smp_info->p1;
  int p2 =  p_smp_info->p2;

  printf("Size: %d\n", size);
  if (p1 >= 0)
    printf("p1  : %d \%%\n", p1);
  else
    printf("p1  : unknown\n");

  if (p2 >= 0)
    printf("p2  : %d \%%\n", p2);
  else
    printf("p2  : unknown\n");

  printf("\nMen Pref\n");
  SMP_Display_Matrix(p_smp_info->pref_m, size, 1);
  printf("\nWomen Pref\n");
  SMP_Display_Matrix(p_smp_info->pref_w, size, 1);
}




#ifndef SMTI_NO_MAIN


int gener = 0;
int seed = -1;
int p1 = 0;
int p2 = 0;
int convert = 0;
int exchange_mat = 0;
int read_initial = 1;
char *file_name = NULL;

int size;
SMPInfo smp_info;


int Show_Blocking_Pairs(SMPVector sol_m);
void SMP_Parse_Cmd_Line(int argc, char *argv[]);

#ifndef No_Gcc_Warn_Unused_Result
#define No_Gcc_Warn_Unused_Result(t) if(t)
#endif



/*
 *  MAIN
 *
 */

int
main(int argc, char *argv[])
{
  SMP_Parse_Cmd_Line(argc, argv);

  if (gener)
    {
      if (seed < 0)
	seed = Randomize();
      else
	Randomize_Seed(seed);

      printf("used seed: %d\n", seed);
      printf("Generating problem of size %d into %s\n", size, file_name);
      SMP_Generate_Problem(size, p1, p2, &smp_info);
      SMP_Write_Problem(file_name, &smp_info);
      return 0;
    }


  size = SMP_Load_Problem(file_name, &smp_info);

  if (exchange_mat)
    {
      SMPMatrix tmp = smp_info.pref_m;
      smp_info.pref_m = smp_info.pref_w;
      smp_info.pref_w = tmp;
      if (read_initial)
	printf("matrices are exchanged\n");
    }

  if (convert)
    {
      char file_out[128];
      strcpy(file_out, file_name);
      int format_is_dat = !Has_Dat_Suffix(file_out);
      char *p = Get_Suffix(file_out);
      if (format_is_dat)
	strcpy(p, ".dat");
      else
	strcpy(p , ".smp");

      printf("converting %s to %s\n", file_name, file_out);
      SMP_Write_Problem(file_out, &smp_info);
      
      return 0;
    }

  if (exchange_mat && !read_initial) {
      SMP_Write_Problem(file_name, &smp_info);
    return 0;
  }


  if (read_initial)
    {
      SMPVector sol_m = SMP_Alloc_Vector(size);
      int based_1 = 1, i;
      printf("enter the initial configuration (the women in order):\n");
      for(i = 0; i < size; i++)
	{
	  No_Gcc_Warn_Unused_Result(scanf("%d", &sol_m[i]));
	  if (sol_m[i] == 0)
	    based_1 = 0;
	}
      getchar();                /* the last \n */
      if (based_1) 	  
	{
	  printf("entered solution is 1-based\n");
	  for(i = 0; i < size; i++)
	    sol_m[i]--;
	}
      return !Show_Blocking_Pairs(sol_m);
    }

  /* show problem */

  SMP_Display_Problem(&smp_info, 1);

  return 0;
}



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



int
Show_Blocking_Pairs(SMPVector sol_m)
{
  int m, w_of_m, rank_w_of_m;
  int w, m_of_w, rank_m_of_w, rank_w;
  int m1, rank_m1;
  int i, j, k, z;
  int nb_bp = 0, nb_singles = 0;
  SMPVector sol_w;
  int size = smp_info.size;
  SMPMatrix pref_m = smp_info.pref_m;
  SMPMatrix pref_w = smp_info.pref_w;


  i = Random_Permut_Check(sol_m, size, NULL, 0);
  
  if (i >= 0)
    {
      printf("ERROR: not a valid permutation, error at [%d] = %d\n", i, sol_m[i]);
      return 0;
    }

  sol_w = SMP_Alloc_Vector(size);
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
	  nb_singles++;
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
                  nb_bp++;
                  goto undominated_only; /* to only show undominated blocking-pair */
                }
            }
        }
    undominated_only:
      ;
    }

  free(sol_w);

  printf("# undom BP: %d   singles: %d\n", nb_bp, nb_singles);
  return (nb_bp + nb_singles == 0);
}



#define L(...) do { fprintf(stderr,  __VA_ARGS__); fprintf(stderr, "\n"); } while(0)

/*
 *  PARSE_CMD_LINE
 *
 */
void
SMP_Parse_Cmd_Line(int argc, char *argv[])
{
  int i;

  for(i = 1; i < argc; i++)
    {
      if (argv[i][0] == '-')
	{
	  switch(argv[i][1])
	    {
	    case 'g':
	      if (++i >= argc)
		{
		  L("SIZE expected");
		  exit(1);
		}
	      size = atoi(argv[i]);
	      gener = 1;
	      continue;

	    case 's':
	      if (++i >= argc)
		{
		  L("random SEED expected");
		  exit(1);
		}
	      seed = atoi(argv[i]);
	      continue;

	    case '1':
	      if (++i >= argc)
		{
		  L("random PERCENTAGE expected");
		  exit(1);
		}
	      p1 = atoi(argv[i]);
	      continue;

	    case '2':
	      if (++i >= argc)
		{
		  L("random PERCENTAGE expected");
		  exit(1);
		}
	      p2 = atoi(argv[i]);
	      continue;

	    case 'c':
	      convert = 1;
	      continue;

	    case 'x':
	      exchange_mat = 1;
	      continue;

	    case 'i':
	      read_initial = 1;
	      continue;
	    
	    case 'h':
	      L("Usage: %s [ OPTION ] FILE_NAME", argv[0]);
	      L(" ");
	      L("   -g SIZE     generate a random problem");
	      L("   -s SEED     specify random seed");
	      L("   -1 PERCT    specify p1 probability of incompleteness (as percentage)");
	      L("   -2 PERCT    specify p2 probability of ties (as a percentage)");
	      L("   -c          convert .dat <-> .smp format");
	      L("   -i          read vector and display blocking pairs");
	      L("   -x          echange matrices (the result is written to the file)");
	      L("If no option is given the problem is displayed");
	      exit(0);

	    default:
	      fprintf(stderr, "unrecognized option %s (-h for a help)\n", argv[i]);
	      exit(1);
	    }
	}

      if (file_name == NULL)
	{
	  file_name = argv[i];
	}
      else
	{
	  fprintf(stderr, "unrecognized argument %s (-h for a help)\n", argv[i]);
	  exit(1);
	}
    }

  if (file_name == NULL)
    {
      fprintf(stderr, "SMP file name expected\n");
      exit(1);
    }
}


#endif /* !SMTI_NO_MAIN */


#endif /* _SMTI_UTILS */

