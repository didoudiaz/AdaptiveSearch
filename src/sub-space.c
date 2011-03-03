/*
 *  EXPLORE_SUB_SPACE
 *
 *  All possible permuts of EXPLORE_PERMUT_SIZE are tested
 */

int 
Next_Permutation(int *t, int n)  // generic procedure (only needs the intial t[] is sorted)
{
  int j, k, r, s, temp;

  for(j = n - 2; j >= 0 && t[j] >= t[j+1]; j--)
    ;

  if (j < 0) 
    return 0;

  for(k = n - 1; t[j] >= t[k]; k--)
    ;

  temp = t[j];
  t[j] = t[k];
  t[k] = temp;

  for(r = n - 1, s = j + 1; r > s; r--, s++) 
    {
      temp = t[r];
      t[r] = t[s];
      t[s] = temp;
    }

  return 1;
} 

#if 0
#define PPRINTF(...) printf (__VA_ARGS__)
#else
#define PPRINTF(...) ((void) 0)
#endif

#define EXPLORE_PERMUT_SIZE 5
#define EXPLORE_NB_TRIES 10



int
Explore_Sub_Space(int cost)
{
  static int o[EXPLORE_PERMUT_SIZE]; /* original index */
  static int v[EXPLORE_PERMUT_SIZE]; /* original values */
  static int p[EXPLORE_PERMUT_SIZE]; /* permuted values */
  int k;
  for(k = 0; k < EXPLORE_NB_TRIES;k++)
    {
      int i;
      int x;
      int beg = 0;
      int end = size - EXPLORE_PERMUT_SIZE;
      //printf("****** TRYING TO IMPROVE %d sol =", cost); Display_Solution(sol);
      for(i = 0; i < EXPLORE_PERMUT_SIZE; i++)
	{
	  o[i] = Random_Interval(beg, end);
	  PPRINTF("[%d..%d]=%d(%d)  ", beg, end, o[i], sol[o[i]]);
	  x = v[i] = sol[o[i]];
	  beg = o[i] + 1;
	  end++;
	  // place x in p to keep p sorted
	  int j;
	  for(j = i; --j >= 0 && p[j] >= x; )
	    {
	      p[j + 1] = p[j];
	    }
	  p[j + 1] = x;

	}
      PPRINTF("\n");
#if 0
      printf("\nvalues: ");
      for(i = 0; i < EXPLORE_PERMUT_SIZE; i++)
	printf("%d ", v[i]);
      printf("\n");

      printf("sorted: ");
      for(i = 0; i < EXPLORE_PERMUT_SIZE; i++)
	printf("%d ", p[i]);
      printf("\n");
#endif

      PPRINTF("-----------------\n");
      //Display_Solution(sol);
      PPRINTF("-----------------\n");


      while(Next_Permutation(p, EXPLORE_PERMUT_SIZE))
	{
	  for(i = 0; i < EXPLORE_PERMUT_SIZE; i++)
	    sol[o[i]] = p[i];

	  PPRINTF("\npermutation: ");
	  for(i = 0; i < EXPLORE_PERMUT_SIZE; i++)
	    PPRINTF("%d ", p[i]);

	  x = Cost(NULL);
	  //PPRINTF("   giving cost:%d sol =", x); Display_Solution(sol);


	  if (x < cost)
	    {
	      // printf("FOUND A BETTER !!! %d < %d\n", x, cost);
	      cost = x;
	      return -1;
	    }
	}

      // restore

      for(i = 0; i < EXPLORE_PERMUT_SIZE; i++)
	sol[o[i]] = v[i];
    }
  return -1;
}
