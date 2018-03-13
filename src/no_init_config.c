/*
 *  Adaptive search
 *
 *  Copyright (C) 2002-2011 Daniel Diaz, Philippe Codognet and Salvador Abreu
 *
 *  no_init_config.c: wrapper when user function {Set/Check}_Init_Configuration are not defined
 */

#include <stdio.h>
#include <stdlib.h>

#include "ad_solver.h"



/*
 *  SET_INIT_CONFIGURATION
 *
 *  Sets an initial configuration.
 */

void
Set_Init_Configuration(AdData *p_ad)
{
  Random_Permut(p_ad->sol, p_ad->size, p_ad->actual_value, p_ad->base_value);
}



/*
 *  CHECK_INIT_CONFIGURATION
 *
 *  Checks if an initial configuration is valid
 */

void
Check_Init_Configuration(AdData *p_ad)
{
  int i = Random_Permut_Check(p_ad->sol, p_ad->size, p_ad->actual_value, p_ad->base_value);
  if (i >= 0)
    {
      fprintf(stderr, "not a valid permutation, error at [%d] = %d\n", i, p_ad->sol[i]);
      Random_Permut_Repair(p_ad->sol, p_ad->size, p_ad->actual_value, p_ad->base_value);
      printf("possible repair:\n");
      Display_Solution(p_ad);
      exit(1);
    }
}
