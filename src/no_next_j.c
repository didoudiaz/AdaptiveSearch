/*
 *  Adaptive search
 *
 *  Copyright (C) 2002-2010 Daniel Diaz, Philippe Codognet and Salvador Abreu
 *
 *  no_next_j.c: wrapper when user function Next_J is not defined
 */


int 
Next_J(int i, int j)
{
  if (j < 0)
    j = i;
  return j + 1;
}
