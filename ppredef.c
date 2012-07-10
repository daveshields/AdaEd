/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "config.h"
#include "predef.h"
#include "miscprots.h"
#include "ppredefprots.h"

/* define procedures:
 *	predef_code(str)   str => corresponding predef code (or zero if no such)
 */
    struct predef { 
        char *pretab_name;
        int   pretab_code;
    } pretab[] = {
	{ "ADD_DUR_TIME"           , P_ADD_DUR_TIME           },
	{ "ADD_TIME_DUR"           , P_ADD_TIME_DUR           },
	{ "CLOCK"                  , P_CLOCK                  },
	{ "COL"                    , P_COL                    },
	{ "COL_FILE"               , P_COL_FILE               },
	{ "CURRENT_INPUT"          , P_CURRENT_INPUT          },
	{ "CURRENT_OUTPUT"         , P_CURRENT_OUTPUT         },
	{ "DAY"                    , P_DAY                    },
	{ "DIO_CLOSE"              , P_DIO_CLOSE              },
	{ "DIO_CREATE"             , P_DIO_CREATE             },
	{ "DIO_DELETE"             , P_DIO_DELETE             },
	{ "DIO_END_OF_FILE"        , P_DIO_END_OF_FILE        },
	{ "DIO_FORM"               , P_DIO_FORM               },
	{ "DIO_INDEX"              , P_DIO_INDEX              },
	{ "DIO_IS_OPEN"            , P_DIO_IS_OPEN            },
	{ "DIO_MODE"               , P_DIO_MODE               },
	{ "DIO_NAME"               , P_DIO_NAME               },
	{ "DIO_OPEN"               , P_DIO_OPEN               },
	{ "DIO_READ"               , P_DIO_READ               },
	{ "DIO_READ_FROM"          , P_DIO_READ_FROM          },
	{ "DIO_RESET"              , P_DIO_RESET              },
	{ "DIO_RESET_MODE"         , P_DIO_RESET_MODE         },
	{ "DIO_SET_INDEX"          , P_DIO_SET_INDEX          },
	{ "DIO_SIZE"               , P_DIO_SIZE               },
	{ "DIO_WRITE"              , P_DIO_WRITE              },
	{ "DIO_WRITE_TO"           , P_DIO_WRITE_TO           },
	{ "END_OF_LINE"            , P_END_OF_LINE            },
	{ "END_OF_LINE_FILE"       , P_END_OF_LINE_FILE       },
	{ "END_OF_PAGE"            , P_END_OF_PAGE            },
	{ "END_OF_PAGE_FILE"       , P_END_OF_PAGE_FILE       },
	{ "GET_CHAR_FILE_ITEM"     , P_GET_CHAR_FILE_ITEM     },
	{ "GET_CHAR_ITEM"          , P_GET_CHAR_ITEM          },
	{ "GET_ENUM_FILE_ITEM"     , P_GET_ENUM_FILE_ITEM     },
	{ "GET_ENUM_ITEM"          , P_GET_ENUM_ITEM          },
	{ "GET_ENUM_STRING"        , P_GET_ENUM_STRING        },
	{ "GET_FIXED_FILE_ITEM"    , P_GET_FIXED_FILE_ITEM    },
	{ "GET_FIXED_ITEM"         , P_GET_FIXED_ITEM         },
	{ "GET_FIXED_STRING"       , P_GET_FIXED_STRING       },
	{ "GET_FLOAT_FILE_ITEM"    , P_GET_FLOAT_FILE_ITEM    },
	{ "GET_FLOAT_ITEM"         , P_GET_FLOAT_ITEM         },
	{ "GET_FLOAT_STRING"       , P_GET_FLOAT_STRING       },
	{ "GET_INTEGER_FILE_ITEM"  , P_GET_INTEGER_FILE_ITEM  },
	{ "GET_INTEGER_ITEM"       , P_GET_INTEGER_ITEM       },
	{ "GET_INTEGER_STRING"     , P_GET_INTEGER_STRING     },
	{ "GET_LINE"               , P_GET_LINE               },
	{ "GET_LINE_FILE"          , P_GET_LINE_FILE          },
	{ "GET_STRING_FILE_ITEM"   , P_GET_STRING_FILE_ITEM   },
	{ "GET_STRING_ITEM"        , P_GET_STRING_ITEM        },
	{ "GE_TIME"                , P_GE_TIME                },
	{ "GT_TIME"                , P_GT_TIME                },
	{ "LE_TIME"                , P_LE_TIME                },
	{ "LINE"                   , P_LINE                   },
	{ "LINE_FILE"              , P_LINE_FILE              },
	{ "LINE_LENGTH"            , P_LINE_LENGTH            },
	{ "LINE_LENGTH_FILE"       , P_LINE_LENGTH_FILE       },
	{ "LT_TIME"                , P_LT_TIME                },
	{ "MONTH"                  , P_MONTH                  },
	{ "NEW_LINE"               , P_NEW_LINE               },
	{ "NEW_LINE_FILE"          , P_NEW_LINE_FILE          },
	{ "NEW_PAGE"               , P_NEW_PAGE               },
	{ "NEW_PAGE_FILE"          , P_NEW_PAGE_FILE          },
	{ "PAGE"                   , P_PAGE                   },
	{ "PAGE_FILE"              , P_PAGE_FILE              },
	{ "PAGE_LENGTH"            , P_PAGE_LENGTH            },
	{ "PAGE_LENGTH_FILE"       , P_PAGE_LENGTH_FILE       },
	{ "PUT_CHAR_FILE_ITEM"     , P_PUT_CHAR_FILE_ITEM     },
	{ "PUT_CHAR_ITEM"          , P_PUT_CHAR_ITEM          },
	{ "PUT_ENUM_FILE_ITEM"     , P_PUT_ENUM_FILE_ITEM     },
	{ "PUT_ENUM_ITEM"          , P_PUT_ENUM_ITEM          },
	{ "PUT_ENUM_STRING"        , P_PUT_ENUM_STRING        },
	{ "PUT_FIXED_FILE_ITEM"    , P_PUT_FIXED_FILE_ITEM    },
	{ "PUT_FIXED_ITEM"         , P_PUT_FIXED_ITEM         },
	{ "PUT_FIXED_STRING"       , P_PUT_FIXED_STRING       },
	{ "PUT_FLOAT_FILE_ITEM"    , P_PUT_FLOAT_FILE_ITEM    },
	{ "PUT_FLOAT_ITEM"         , P_PUT_FLOAT_ITEM         },
	{ "PUT_FLOAT_STRING"       , P_PUT_FLOAT_STRING       },
	{ "PUT_INTEGER_FILE_ITEM"  , P_PUT_INTEGER_FILE_ITEM  },
	{ "PUT_INTEGER_ITEM"       , P_PUT_INTEGER_ITEM       },
	{ "PUT_INTEGER_STRING"     , P_PUT_INTEGER_STRING     },
	{ "PUT_LINE"               , P_PUT_LINE               },
	{ "PUT_LINE_FILE"          , P_PUT_LINE_FILE          },
	{ "PUT_STRING_FILE_ITEM"   , P_PUT_STRING_FILE_ITEM   },
	{ "PUT_STRING_ITEM"        , P_PUT_STRING_ITEM        },
	{ "P_FILE"                 , P_P_FILE                 },
	{ "P_IN"                   , P_P_IN                   },
	{ "P_OUT"                  , P_P_OUT                  },
	{ "SECONDS"                , P_SECONDS                },
	{ "SET_COL"                , P_SET_COL                },
	{ "SET_COL_FILE"           , P_SET_COL_FILE           },
	{ "SET_INPUT"              , P_SET_INPUT              },
	{ "SET_LINE"               , P_SET_LINE               },
	{ "SET_LINE_FILE"          , P_SET_LINE_FILE          },
	{ "SET_LINE_LENGTH"        , P_SET_LINE_LENGTH        },
	{ "SET_LINE_LENGTH_FILE"   , P_SET_LINE_LENGTH_FILE   },
	{ "SET_OUTPUT"             , P_SET_OUTPUT             },
	{ "SET_PAGE_LENGTH"        , P_SET_PAGE_LENGTH        },
	{ "SET_PAGE_LENGTH_FILE"   , P_SET_PAGE_LENGTH_FILE   },
	{ "SIO_CLOSE"              , P_SIO_CLOSE              },
	{ "SIO_CREATE"             , P_SIO_CREATE             },
	{ "SIO_DELETE"             , P_SIO_DELETE             },
	{ "SIO_END_OF_FILE"        , P_SIO_END_OF_FILE        },
	{ "SIO_FORM"               , P_SIO_FORM               },
	{ "SIO_IS_OPEN"            , P_SIO_IS_OPEN            },
	{ "SIO_MODE"               , P_SIO_MODE               },
	{ "SIO_NAME"               , P_SIO_NAME               },
	{ "SIO_OPEN"               , P_SIO_OPEN               },
	{ "SIO_READ"               , P_SIO_READ               },
	{ "SIO_RESET"              , P_SIO_RESET              },
	{ "SIO_RESET_MODE"         , P_SIO_RESET_MODE         },
	{ "SIO_WRITE"              , P_SIO_WRITE              },
	{ "SKIP_LINE"              , P_SKIP_LINE              },
	{ "SKIP_LINE_FILE"         , P_SKIP_LINE_FILE         },
	{ "SKIP_PAGE"              , P_SKIP_PAGE              },
	{ "SKIP_PAGE_FILE"         , P_SKIP_PAGE_FILE         },
	{ "SPLIT"                  , P_SPLIT                  },
	{ "STANDARD_INPUT"         , P_STANDARD_INPUT         },
	{ "STANDARD_OUTPUT"        , P_STANDARD_OUTPUT        },
	{ "SUB_TIME_DUR"           , P_SUB_TIME_DUR           },
	{ "SUB_TIME_TIME"          , P_SUB_TIME_TIME          },
	{ "TIME_OF"                , P_TIME_OF                },
	{ "TIO_CLOSE"              , P_TIO_CLOSE              },
	{ "TIO_CREATE"             , P_TIO_CREATE             },
	{ "TIO_DELETE"             , P_TIO_DELETE             },
	{ "TIO_END_OF_FILE"        , P_TIO_END_OF_FILE        },
	{ "TIO_END_OF_FILE_FILE"   , P_TIO_END_OF_FILE_FILE   },
	{ "TIO_FORM"               , P_TIO_FORM               },
	{ "TIO_IS_OPEN"            , P_TIO_IS_OPEN            },
	{ "TIO_MODE"               , P_TIO_MODE               },
	{ "TIO_NAME"               , P_TIO_NAME               },
	{ "TIO_OPEN"               , P_TIO_OPEN               },
	{ "TIO_RESET"              , P_TIO_RESET              },
	{ "TIO_RESET_MODE"         , P_TIO_RESET_MODE         },
	{ "YEAR"                   , P_YEAR                   },
	{ (char *)0, 0 }
    };
int predef_code(char *name)									/*;predef_code*/
{
	/* return code given predef opcode name */
    int i;
    
    for (i = 0; ; i++) {
		if (pretab[i].pretab_name == (char *)0) chaos("predef_code failed");
		if (strcmp(pretab[i].pretab_name, name) == 0 ) break;
    }
    return pretab[i].pretab_code;
}
