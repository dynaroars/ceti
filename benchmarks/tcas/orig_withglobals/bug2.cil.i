# 1 "./bug2.cil.c"
# 1 "<command-line>"
# 1 "./bug2.cil.c"



typedef unsigned long size_t;
typedef long __off_t;
typedef long __off64_t;
struct _IO_FILE;
struct _IO_FILE;
typedef struct _IO_FILE FILE;
struct _IO_FILE;
typedef void _IO_lock_t;
struct _IO_marker {
   struct _IO_marker *_next ;
   struct _IO_FILE *_sbuf ;
   int _pos ;
};
struct _IO_FILE {
   int _flags ;
   char *_IO_read_ptr ;
   char *_IO_read_end ;
   char *_IO_read_base ;
   char *_IO_write_base ;
   char *_IO_write_ptr ;
   char *_IO_write_end ;
   char *_IO_buf_base ;
   char *_IO_buf_end ;
   char *_IO_save_base ;
   char *_IO_backup_base ;
   char *_IO_save_end ;
   struct _IO_marker *_markers ;
   struct _IO_FILE *_chain ;
   int _fileno ;
   int _flags2 ;
   __off_t _old_offset ;
   unsigned short _cur_column ;
   signed char _vtable_offset ;
   char _shortbuf[1] ;
   _IO_lock_t *_lock ;
   __off64_t _offset ;
   void *__pad1 ;
   void *__pad2 ;
   void *__pad3 ;
   void *__pad4 ;
   size_t __pad5 ;
   int _mode ;
   char _unused2[(15UL * sizeof(int ) - 4UL * sizeof(void *)) - sizeof(size_t )] ;
};
typedef int bool;
extern struct _IO_FILE *stdout ;
extern int fprintf(FILE * __restrict __stream , char const * __restrict __format
                   , ...) ;
int Cur_Vertical_Sep ;
bool High_Confidence ;
bool Two_of_Three_Reports_Valid ;
int Own_Tracked_Alt ;
int Own_Tracked_Alt_Rate ;
int Other_Tracked_Alt ;
int Alt_Layer_Value ;
int Positive_RA_Alt_Thresh[4] ;
int Up_Separation ;
int Down_Separation ;
int Other_RAC ;
int Other_Capability ;
int Climb_Inhibit ;
int ALIM(void)
{


  {
  if (Alt_Layer_Value == 0) {
    return (400);
  } else
  if (Alt_Layer_Value == 1) {
    return (500);
  } else
  if (Alt_Layer_Value == 2) {
    return (640);
  } else {
    return (740);
  }
}
}
int Inhibit_Biased_Climb(void)
{
  int tmp ;

  {
  if (Climb_Inhibit) {
    tmp = Up_Separation;
  } else {
    tmp = Up_Separation;
  }
  return (tmp);
}
}
bool Own_Below_Threat(void) ;
bool Own_Above_Threat(void) ;
bool Non_Crossing_Biased_Climb(void)
{
  int upward_preferred ;
  bool result ;
  int tmp ;
  int tmp___0 ;
  int tmp___1 ;
  int tmp___2 ;
  int tmp___3 ;
  int tmp___4 ;
  int tmp___5 ;
  int tmp___6 ;

  {
  tmp = Inhibit_Biased_Climb();
  upward_preferred = tmp > Down_Separation;
  if (upward_preferred) {
    tmp___0 = Own_Below_Threat();
    if (tmp___0) {
      tmp___1 = Own_Below_Threat();
      if (tmp___1) {
        tmp___2 = ALIM();
        if (Down_Separation >= tmp___2) {
          tmp___3 = 0;
        } else {
          tmp___3 = 1;
        }
      } else {
        tmp___3 = 0;
      }
    } else {
      tmp___3 = 1;
    }
    result = tmp___3;
  } else {
    tmp___4 = Own_Above_Threat();
    if (tmp___4) {
      if (Cur_Vertical_Sep >= 300) {
        tmp___5 = ALIM();
        if (Up_Separation >= tmp___5) {
          tmp___6 = 1;
        } else {
          tmp___6 = 0;
        }
      } else {
        tmp___6 = 0;
      }
    } else {
      tmp___6 = 0;
    }
    result = tmp___6;
  }
  return (result);
}
}
bool Non_Crossing_Biased_Descend(void)
{
  int upward_preferred ;
  bool result ;
  int tmp ;
  int tmp___0 ;
  int tmp___1 ;
  int tmp___2 ;
  int tmp___3 ;
  int tmp___4 ;
  int tmp___5 ;
  int tmp___6 ;

  {
  tmp = Inhibit_Biased_Climb();
  upward_preferred = tmp > Down_Separation;
  if (upward_preferred) {
    tmp___0 = Own_Below_Threat();
    if (tmp___0) {
      if (Cur_Vertical_Sep >= 300) {
        tmp___1 = ALIM();
        if (Down_Separation >= tmp___1) {
          tmp___2 = 1;
        } else {
          tmp___2 = 0;
        }
      } else {
        tmp___2 = 0;
      }
    } else {
      tmp___2 = 0;
    }
    result = tmp___2;
  } else {
    tmp___3 = Own_Above_Threat();
    if (tmp___3) {
      tmp___4 = Own_Above_Threat();
      if (tmp___4) {
        tmp___5 = ALIM();
        if (Up_Separation >= tmp___5) {
          tmp___6 = 1;
        } else {
          tmp___6 = 0;
        }
      } else {
        tmp___6 = 0;
      }
    } else {
      tmp___6 = 1;
    }
    result = tmp___6;
  }
  return (result);
}
}
bool Own_Below_Threat(void)
{


  {
  return (Own_Tracked_Alt < Other_Tracked_Alt);
}
}
bool Own_Above_Threat(void)
{


  {
  return (Other_Tracked_Alt < Own_Tracked_Alt);
}
}
int alt_sep_test(void)
{
  bool enabled ;
  bool tcas_equipped ;
  bool intent_not_known ;
  bool need_upward_RA ;
  bool need_downward_RA ;
  int alt_sep ;
  int tmp ;
  int tmp___0 ;
  bool tmp___1 ;
  bool tmp___2 ;
  int tmp___3 ;
  bool tmp___4 ;
  bool tmp___5 ;
  int tmp___6 ;

  {
  if (High_Confidence) {
    if (Own_Tracked_Alt_Rate <= 600) {
      if (Cur_Vertical_Sep > 600) {
        tmp = 1;
      } else {
        tmp = 0;
      }
    } else {
      tmp = 0;
    }
  } else {
    tmp = 0;
  }
  enabled = tmp;
  tcas_equipped = Other_Capability == 1;
  if (Two_of_Three_Reports_Valid) {
    if (Other_RAC == 0) {
      tmp___0 = 1;
    } else {
      tmp___0 = 0;
    }
  } else {
    tmp___0 = 0;
  }
  intent_not_known = tmp___0;
  alt_sep = 0;
  if (enabled) {
    if (tcas_equipped) {
      if (intent_not_known) {
        goto _L___0;
      } else {
        goto _L___1;
      }
    } else
    _L___1:
    if (! tcas_equipped) {
      _L___0:
      tmp___1 = Non_Crossing_Biased_Climb();
      if (tmp___1) {
        tmp___2 = Own_Below_Threat();
        if (tmp___2) {
          tmp___3 = 1;
        } else {
          tmp___3 = 0;
        }
      } else {
        tmp___3 = 0;
      }
      need_upward_RA = tmp___3;
      tmp___4 = Non_Crossing_Biased_Descend();
      if (tmp___4) {
        tmp___5 = Own_Above_Threat();
        if (tmp___5) {
          tmp___6 = 1;
        } else {
          tmp___6 = 0;
        }
      } else {
        tmp___6 = 0;
      }
      need_downward_RA = tmp___6;
      if (need_upward_RA) {
        if (need_downward_RA) {
          alt_sep = 0;
        } else {
          goto _L;
        }
      } else
      _L:
      if (need_upward_RA) {
        alt_sep = 1;
      } else
      if (need_downward_RA) {
        alt_sep = 2;
      } else {
        alt_sep = 0;
      }
    }
  }
  return (alt_sep);
}
}
int mainQ(int a1 , int a2 , int a3 , int a4 , int a5 , int a6 , int a7 , int a8 ,
          int a9 , int a10 , int a11 , int a12 )
{
  int tmp ;

  {
  Cur_Vertical_Sep = a1;
  High_Confidence = a2;
  Two_of_Three_Reports_Valid = a3;
  Own_Tracked_Alt = a4;
  Own_Tracked_Alt_Rate = a5;
  Other_Tracked_Alt = a6;
  Alt_Layer_Value = a7;
  Up_Separation = a8;
  Down_Separation = a9;
  Other_RAC = a10;
  Other_Capability = a11;
  Climb_Inhibit = a12;
  tmp = alt_sep_test();
  return (tmp);
}
}
extern int ( atoi)() ;
int main(int argc , char **argv )
{
  int tmp ;
  int tmp___0 ;
  int tmp___1 ;
  int tmp___2 ;
  int tmp___3 ;
  int tmp___4 ;
  int tmp___5 ;
  int tmp___6 ;
  int tmp___7 ;
  int tmp___8 ;
  int tmp___9 ;
  int tmp___10 ;
  int tmp___11 ;

  {
  tmp = atoi(*(argv + 12));
  tmp___0 = atoi(*(argv + 11));
  tmp___1 = atoi(*(argv + 10));
  tmp___2 = atoi(*(argv + 9));
  tmp___3 = atoi(*(argv + 8));
  tmp___4 = atoi(*(argv + 7));
  tmp___5 = atoi(*(argv + 6));
  tmp___6 = atoi(*(argv + 5));
  tmp___7 = atoi(*(argv + 4));
  tmp___8 = atoi(*(argv + 3));
  tmp___9 = atoi(*(argv + 2));
  tmp___10 = atoi(*(argv + 1));
  tmp___11 = mainQ(tmp___10, tmp___9, tmp___8, tmp___7, tmp___6, tmp___5, tmp___4,
                   tmp___3, tmp___2, tmp___1, tmp___0, tmp);
  fprintf((FILE * __restrict )stdout, (char const * __restrict )"%d\n", tmp___11);
  return (0);
}
}
