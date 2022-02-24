#include <assert.h>
#include <stdio.h>

#include "vmtypes.h"
#include "engine.h"
#include "opcode.h"
#include "memory.h"
#include "fail.h"

typedef enum { Cb, Ib4, Lb, Lb32, Lb64, Lb96, Lb128, Ob4 } reg_bank_t;

static void* memory_start;
static void* memory_end;

static value_t* R[8];          /* (pseudo)base registers */

static value_t* get_Ob() { return R[Ob4] - 4; }
static value_t* get_Lb() { return R[Lb]; }
static value_t* get_Ib() { return R[Ib4] - 4; }

static void set_Ib(value_t* new_value) { R[Ib4] = new_value + 4; }
static void set_Lb(value_t* new_value) {
  R[Lb] = new_value;
  R[Lb32] = new_value + 32;
  R[Lb64] = new_value + 64;
  R[Lb96] = new_value + 96;
  R[Lb128] = new_value + 128;
}
static void set_Ob(value_t* new_value) { R[Ob4] = new_value + 4; }

void engine_setup(void) {
  memory_start = memory_get_start();
  memory_end = memory_get_end();

  engine_set_Cb(memory_start);
  set_Ib(memory_start);
  set_Lb(memory_start);
  set_Ob(memory_start);
}

void engine_set_Cb(value_t* new_value) { R[Cb] = new_value; }

void engine_cleanup(void) {
  // nothing to do
}

void engine_emit(instr_t instr, instr_t** instr_ptr) {
  if ((void*)(*instr_ptr + 1) > memory_end)
    fail("not enough memory to load code");
  **instr_ptr = instr;
  *instr_ptr += 1;
}

// Virtual <-> physical address translation

static void* addr_v_to_p(value_t v_addr) {
  return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
  assert(memory_start <= p_addr && p_addr <= memory_end);
  return (value_t)((char*)p_addr - (char*)memory_start);
}

// Instruction decoding

static reg_bank_t reg_bank(reg_id_t r) {
  return r >> 5;
}

static unsigned int reg_index(reg_id_t r) {
  return r & 0x1F;
}

static unsigned int instr_extract_u(instr_t instr, int start, int len) {
  return (instr >> start) & ((1 << len) - 1);
}

static int instr_extract_s(instr_t instr, int start, int len) {
  int bits = (int)instr_extract_u(instr, start, len);
  int m = 1 << (len - 1);
  return (bits ^ m) - m;
}

static opcode_t instr_opcode(instr_t instr) {
  unsigned int opcode = instr_extract_u(instr, 27, 5);
  return (opcode_t)opcode;
}

static reg_id_t instr_ra(instr_t instr) {
  return (reg_id_t)instr_extract_u(instr, 0, 8);
}

static reg_id_t instr_rb(instr_t instr) {
  return (reg_id_t)instr_extract_u(instr, 8, 8);
}

static reg_id_t instr_rc(instr_t instr) {
  return (reg_id_t)instr_extract_u(instr, 16, 8);
}

static int instr_d(instr_t instr) {
  return instr_extract_s(instr, 16, 11);
}

// Call/return

static value_t* call(value_t target_pc,
                     value_t ib,
                     value_t lb,
                     value_t ob,
                     value_t ret_pc) {
  value_t* ob_p = get_Ob();
  ob_p[0] = ib;
  ob_p[1] = lb;
  ob_p[2] = ob;
  ob_p[3] = ret_pc;
  set_Ib(ob_p);
  set_Lb(memory_start);
  set_Ob(memory_start);
  return addr_v_to_p(target_pc);
}

static value_t* ret(value_t ret_value) {
  value_t* ib_p = get_Ib();
  value_t* ret_pc = addr_v_to_p(ib_p[3]);
  set_Ob(addr_v_to_p(ib_p[2]));
  set_Lb(addr_v_to_p(ib_p[1]));
  set_Ib(addr_v_to_p(ib_p[0]));
  R[Ob4][0] = ret_value;
  return ret_pc;
}

// (Pseudo-)register access

#define Ra (R[reg_bank(instr_ra(*pc))][reg_index(instr_ra(*pc))])
#define Rb (R[reg_bank(instr_rb(*pc))][reg_index(instr_rb(*pc))])
#define Rc (R[reg_bank(instr_rc(*pc))][reg_index(instr_rc(*pc))])

#define GOTO_NEXT goto *labels[instr_opcode(*pc)]

value_t engine_run() {
  void** labels[] =
    {
     [opcode_ADD]     = &&l_ADD,
     [opcode_SUB]     = &&l_SUB,
     [opcode_MUL]     = &&l_MUL,
     [opcode_DIV]     = &&l_DIV,
     [opcode_MOD]     = &&l_MOD,
     [opcode_LSL]     = &&l_LSL,
     [opcode_LSR]     = &&l_LSR,
     [opcode_AND]     = &&l_AND,
     [opcode_OR]      = &&l_OR,
     [opcode_XOR]     = &&l_XOR,
     [opcode_JLT]     = &&l_JLT,
     [opcode_JLE]     = &&l_JLE,
     [opcode_JEQ]     = &&l_JEQ,
     [opcode_JNE]     = &&l_JNE,
     [opcode_JI]      = &&l_JI,
     [opcode_CALL_NI] = &&l_CALL_NI,
     [opcode_CALL_ND] = &&l_CALL_ND,
     [opcode_CALL_TI] = &&l_CALL_TI,
     [opcode_CALL_TD] = &&l_CALL_TD,
     [opcode_RET]     = &&l_RET,
     [opcode_HALT]    = &&l_HALT,
     [opcode_LDLO]    = &&l_LDLO,
     [opcode_LDHI]    = &&l_LDHI,
     [opcode_MOVE]    = &&l_MOVE,
     [opcode_RALO]    = &&l_RALO,
     [opcode_BALO]    = &&l_BALO,
     [opcode_BSIZ]    = &&l_BSIZ,
     [opcode_BTAG]    = &&l_BTAG,
     [opcode_BGET]    = &&l_BGET,
     [opcode_BSET]    = &&l_BSET,
     [opcode_BREA]    = &&l_BREA,
     [opcode_BWRI]    = &&l_BWRI,
    };

  instr_t* pc = memory_start;
  set_Ib(memory_start);
  set_Lb(memory_start);
  set_Ob(memory_start);

  GOTO_NEXT;

 l_ADD: {
    Ra = Rb + Rc;
    pc += 1;
  } GOTO_NEXT;

 l_SUB: {
    Ra = Rb - Rc;
    pc += 1;
  } GOTO_NEXT;

 l_MUL: {
    Ra = Rb * Rc;
    pc += 1;
  } GOTO_NEXT;

 l_DIV: {
    Ra = (value_t)((svalue_t)Rb / (svalue_t)Rc);
    pc += 1;
  } GOTO_NEXT;

 l_MOD: {
    Ra = (value_t)((svalue_t)Rb % (svalue_t)Rc);
    pc += 1;
  } GOTO_NEXT;

 l_LSL: {
    Ra = Rb << (Rc & 0x1F);
    pc += 1;
  } GOTO_NEXT;

 l_LSR: {
    Ra = (value_t)((svalue_t)Rb >> (Rc & 0x1F));
    pc += 1;
  } GOTO_NEXT;

 l_AND: {
    Ra = Rb & Rc;
    pc += 1;
  } GOTO_NEXT;

 l_OR: {
    Ra = Rb | Rc;
    pc += 1;
  } GOTO_NEXT;

 l_XOR: {
    Ra = Rb ^ Rc;
    pc += 1;
  } GOTO_NEXT;

 l_JLT: {
    pc += ((svalue_t)Ra < (svalue_t)Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JLE: {
    pc += ((svalue_t)Ra <= (svalue_t)Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JEQ: {
    pc += (Ra == Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JNE: {
    pc += (Ra != Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JI: {
    pc += instr_extract_s(*pc, 0, 27);
  } GOTO_NEXT;

 l_CALL_NI: {
    pc = call(Ra,
              addr_p_to_v(get_Ib()),
              addr_p_to_v(get_Lb()),
              addr_p_to_v(get_Ob()),
              addr_p_to_v(pc + 1));
  } GOTO_NEXT;

 l_CALL_ND: {
    pc = call(addr_p_to_v(pc + instr_extract_s(*pc, 0, 27)),
              addr_p_to_v(get_Ib()),
              addr_p_to_v(get_Lb()),
              addr_p_to_v(get_Ob()),
              addr_p_to_v(pc + 1));
  } GOTO_NEXT;

 l_CALL_TI: {
    value_t* ib_p = get_Ib();
    pc = call(Ra, ib_p[0], ib_p[1], ib_p[2], ib_p[3]);
  } GOTO_NEXT;

 l_CALL_TD: {
    value_t target_pc = addr_p_to_v(pc + instr_extract_s(*pc, 0, 27));
    value_t* ib_p = get_Ib();
    pc = call(target_pc, ib_p[0], ib_p[1], ib_p[2], ib_p[3]);
  } GOTO_NEXT;

 l_RET: {
    pc = ret(Ra);
  } GOTO_NEXT;

 l_HALT: {
    return Ra;
  }

 l_LDLO: {
    Ra = (value_t)instr_extract_s(*pc, 8, 19);
    pc += 1;
  } GOTO_NEXT;

 l_LDHI: {
    Ra = ((value_t)instr_extract_u(*pc, 8, 16) << 16) | (Ra & 0xFFFF);
    pc += 1;
  } GOTO_NEXT;

 l_MOVE: {
    Ra = Rb;
    pc += 1;
  } GOTO_NEXT;

 l_RALO: {
    value_t l_size = instr_extract_u(*pc, 0, 8);
    value_t o_size = instr_extract_u(*pc, 8, 8);
    roots_t roots = { .Ib = get_Ib(), .Lb = get_Lb(), .Ob = get_Ob() };
    if (l_size == 0) {
      roots.Ob = memory_allocate(tag_RegisterFrame, o_size, &roots);
    } else if (o_size == 0) {
      roots.Lb = memory_allocate(tag_RegisterFrame, l_size, &roots);
    } else {
      memory_allocate_lb_ob(l_size, o_size, &roots);
    }
    set_Lb(roots.Lb);
    set_Ob(roots.Ob);
    // TODO: write back other roots (for copying GC)
    pc += 1;
  } GOTO_NEXT;

 l_BALO: {
    roots_t roots = { .Ib = get_Ib(), .Lb = get_Lb(), .Ob = get_Ob() };
    value_t* block = memory_allocate(instr_extract_u(*pc, 16, 8), Rb, &roots);
    // TODO: write back roots (for copying GC)
    Ra = addr_p_to_v(block);
    pc += 1;
  } GOTO_NEXT;

 l_BSIZ: {
    Ra = memory_get_block_size(addr_v_to_p(Rb));
    pc += 1;
  } GOTO_NEXT;

 l_BTAG: {
    Ra = memory_get_block_tag(addr_v_to_p(Rb));
    pc += 1;
  } GOTO_NEXT;

 l_BGET: {
    value_t* block = addr_v_to_p(Rb);
    value_t index = Rc;
    assert(index < memory_get_block_size(block));
    Ra = block[index];
    pc += 1;
  } GOTO_NEXT;

 l_BSET: {
    value_t* block = addr_v_to_p(Rb);
    value_t index = Rc;
    assert(index < memory_get_block_size(block));
    block[index] = Ra;
    pc += 1;
  } GOTO_NEXT;

 l_BREA: {
    int maybe_byte = getchar_unlocked();
    Ra = (value_t)(maybe_byte != EOF ? maybe_byte : -1);
    pc += 1;
  } GOTO_NEXT;

 l_BWRI: {
    uint8_t byte = (uint8_t)Ra;
    putchar_unlocked(byte);
    pc += 1;
  } GOTO_NEXT;
}
