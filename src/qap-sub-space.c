/*
 *  EXPLORE_SUB_SPACE
 *
 *  Computes next_i and next_j, the 2 variables to swap.
 *  All possible permuts of EXPLORE NB_PERMUTS are tested
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

#define EXPLORE_NB_PERMUTS 5
#define EXPLORE_NB_TRIES 1



int
Explore_Sub_Space(int cost)
{
  static int o[EXPLORE_NB_PERMUTS]; /* original index */
  static int v[EXPLORE_NB_PERMUTS]; /* original values */
  static int p[EXPLORE_NB_PERMUTS]; /* permuted values */
  int k;
  for(k = 0; k < EXPLORE_NB_TRIES;k++)
    {
      int i;
      int x;
      int beg = 0;
      int end = n - EXPLORE_NB_PERMUTS;
      //printf("****** TRYING TO IMPROVE %d sol =", cost); Display_Solution(sol);
      for(i = 0; i < EXPLORE_NB_PERMUTS; i++)
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
      for(i = 0; i < EXPLORE_NB_PERMUTS; i++)
	printf("%d ", v[i]);
      printf("\n");

      printf("sorted: ");
      for(i = 0; i < EXPLORE_NB_PERMUTS; i++)
	printf("%d ", p[i]);
      printf("\n");
#endif

      PPRINTF("-----------------\n");
      //Display_Solution(sol);
      PPRINTF("-----------------\n");


      while(Next_Permutation(p, EXPLORE_NB_PERMUTS))
	{
	  for(i = 0; i < EXPLORE_NB_PERMUTS; i++)
	    sol[o[i]] = p[i];

	  PPRINTF("\npermutation: ");
	  for(i = 0; i < EXPLORE_NB_PERMUTS; i++)
	    PPRINTF("%d ", p[i]);

	  x = Cost(NULL);
	  //PPRINTF("   giving cost:%d sol =", x); Display_Solution(sol);


	  if (x < cost)
	    {
	      printf("FOUND A BETTER !!! %d < %d\n", x, cost);
	      cost = x;
	      return -1;
	    }
	}

      // restore

      for(i = 0; i < EXPLORE_NB_PERMUTS; i++)
	sol[o[i]] = v[i];
    }
  return -1;
}
