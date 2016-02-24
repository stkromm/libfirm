/*
 * Copyright (C) 1995-2008 University of Karlsruhe.  All right reserved.
 *
 * This file is part of libFirm.
 *
 * This file may be distributed and/or modified under the terms of the
 * GNU General Public License version 2 as published by the Free Software
 * Foundation and appearing in the file LICENSE.GPL included in the
 * packaging of this file.
 *
 * Licensees holding valid libFirm Professional Edition licenses may use
 * this file in accordance with the libFirm Commercial License.
 * Agreement provided with the Software.
 *
 * This file is provided AS IS with NO WARRANTY OF ANY KIND, INCLUDING THE
 * WARRANTY OF DESIGN, MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE.
 */

/**
 * @file
 * @brief     Error handling for libFirm
 * @author    Michael Beck
 */
#include "config.h"

#include <stdlib.h>

#include <stdio.h>
#include <stdarg.h>
#include "error.h"
#include "irprintf.h"

NORETURN (panic)(char const *const file, int const line, char const *const func, char const *const fmt, ...)
{
	va_list ap;

	fprintf(stderr, "%s:%d: libFirm panic in %s: ", file, line, func);
	va_start(ap, fmt);
	ir_vfprintf(stderr, fmt, ap);
	va_end(ap);
	putc('\n', stderr);
	abort();
}