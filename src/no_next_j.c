/*
 *  Adaptive search
 *
 *  Copyright (C) 2002-2011 Daniel Diaz, Philippe Codognet and Salvador Abreu
 *
 *  no_next_j.c: wrapper when user function Next_J is not defined
 */


/* if exhaustive generates for a i: i+1, i+2, ...
 * if not exhaustive: 0, 1, 2, ...
 */

int 
Next_J(int i, int j, int exhaustive)
{
  if (j < 0 && exhaustive)
    j = i;

  return j + 1;
}
