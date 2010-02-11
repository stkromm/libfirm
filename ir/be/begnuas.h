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
 * @brief       Dumps global variables and constants as gas assembler.
 * @author      Christian Wuerdig, Matthias Braun
 * @date        04.11.2005
 * @version     $Id$
 */
#ifndef FIRM_BE_BEGNUAS_H
#define FIRM_BE_BEGNUAS_H

#include <stdbool.h>
#include "be.h"
#include "beemitter.h"

typedef enum section_t {
	GAS_SECTION_TEXT,   /**< text section - contains program code */
	GAS_SECTION_DATA,   /**< data section - contains arbitrary data */
	GAS_SECTION_RODATA, /**< rodata section - contains read-only data */
	GAS_SECTION_BSS,    /**< bss section - contains uninitialized data */
	GAS_SECTION_TLS_DATA, /**< thread local storage section */
	GAS_SECTION_TLS_BSS,  /**< thread local storage yero initialized */
	GAS_SECTION_CONSTRUCTORS,   /**< ctors section */
	GAS_SECTION_DESTRUCTORS,    /**< dtors section */
	GAS_SECTION_CSTRING, /**< section for constant strings */
	GAS_SECTION_PIC_TRAMPOLINES, /**< trampolines for pic codes */
	GAS_SECTION_PIC_SYMBOLS,     /**< contains resolved pic symbols */
	GAS_SECTION_LAST = GAS_SECTION_PIC_SYMBOLS
} be_gas_section_t;

typedef enum object_file_format_t {
	OBJECT_FILE_FORMAT_ELF,    /**< Executable and Linkable Format (unixes) */
	OBJECT_FILE_FORMAT_COFF,   /**< Common Object File Format (Windows) */
	OBJECT_FILE_FORMAT_MACH_O, /**< Mach Object File Format (OS/X) */
	OBJECT_FILE_FORMAT_LAST = OBJECT_FILE_FORMAT_MACH_O
} object_file_format_t;

/** The variable where the GAS dialect is stored. */
extern object_file_format_t be_gas_object_file_format;
extern bool                 be_gas_emit_types;
/**
 * the .type directive needs to specify @function, #function or %function
 * depending on the target architecture (yay)
 */
extern char             be_gas_elf_type_char;

/**
 * Generate all entities.
 * @param main_env          the main backend environment
 * @param emit_commons      if non-zero, emit commons (non-local uninitialized entities)
 */
void be_gas_emit_decls(const be_main_env_t *main_env);

/**
 * Switch the current output section to the given out.
 *
 * @param section  the new output section
 */
void be_gas_emit_switch_section(be_gas_section_t section);

/**
 * emit assembler instructions necessary before starting function code
 */
void be_gas_emit_function_prolog(const ir_entity *entity,
                                 unsigned po2alignment);

void be_gas_emit_function_epilog(const ir_entity *entity);

/**
 * emit ld_ident of an entity and performs additional mangling if necessary.
 * (mangling is necessary for ir_visibility_private for example).
 * Emits a block label for type_code entities.
 */
void be_gas_emit_entity(const ir_entity *entity);

/**
 * Return the label prefix for labeled blocks.
 */
const char *be_gas_block_label_prefix(void);

/**
 * Return the label prefix for labeled instructions.
 */
const char *be_gas_insn_label_prefix(void);

#endif
