// See LICENSE for license details.

#include "cachesim.h"
#include "common.h"
#include <cstdlib>
#include <iostream>
#include <iomanip>
#include <stdio.h>
#include <stdlib.h>

cache_sim_t::cache_sim_t(size_t _sets, size_t _ways, size_t _linesz, const char* _name)
 : sets(_sets), ways(_ways), linesz(_linesz), name(_name)
{
  init();
}

static void help()
{
  std::cerr << "Cache configurations must be of the form" << std::endl;
  std::cerr << "  sets:ways:blocksize" << std::endl;
  std::cerr << "where sets, ways, and blocksize are positive integers, with" << std::endl;
  std::cerr << "sets and blocksize both powers of two and blocksize at least 8." << std::endl;
  exit(1);
}

cache_sim_t* cache_sim_t::construct(const char* config, const char* name)
{
  const char* wp = strchr(config, ':');
  if (!wp++) help();
  const char* bp = strchr(wp, ':');
  if (!bp++) help();

  size_t sets = atoi(std::string(config, wp).c_str());
  size_t ways = atoi(std::string(wp, bp).c_str());
  size_t linesz = atoi(bp);

  if (ways > 4 /* empirical */ && sets == 1)
    return new fa_cache_sim_t(ways, linesz, name);
  return new cache_sim_t(sets, ways, linesz, name);
}

void cache_sim_t::init()
{
  if(sets == 0 || (sets & (sets-1)))
    help();
  if(linesz < 8 || (linesz & (linesz-1)))
    help();

  idx_shift = 0;
  for (size_t x = linesz; x; x >>= 1)
    idx_shift++;

  tags = new uint64_t[sets*ways]();
  victim_cache = new uint64_t[3]();
  read_accesses = 0;
  read_misses = 0;
  bytes_read = 0;
  write_accesses = 0;
  write_misses = 0;
  bytes_written = 0;
  writebacks = 0;

  miss_handler = NULL;
}

cache_sim_t::cache_sim_t(const cache_sim_t& rhs)
 : sets(rhs.sets), ways(rhs.ways), linesz(rhs.linesz),
   idx_shift(rhs.idx_shift), name(rhs.name)
{
  tags = new uint64_t[sets*ways];
  memcpy(tags, rhs.tags, sets*ways*sizeof(uint64_t));
}

cache_sim_t::~cache_sim_t()
{
  print_stats();
  delete [] tags;
}

void cache_sim_t::print_stats()
{
  if(read_accesses + write_accesses == 0)
    return;

  float mr = 100.0f*(read_misses+write_misses)/(read_accesses+write_accesses);

  std::cout << std::setprecision(3) << std::fixed;
  std::cout << name << " ";
  std::cout << "Bytes Read:            " << bytes_read << std::endl;
  std::cout << name << " ";
  std::cout << "Bytes Written:         " << bytes_written << std::endl;
  std::cout << name << " ";
  std::cout << "Read Accesses:         " << read_accesses << std::endl;
  std::cout << name << " ";
  std::cout << "Write Accesses:        " << write_accesses << std::endl;
  std::cout << name << " ";
  std::cout << "Read Misses:           " << read_misses << std::endl;
  std::cout << name << " ";
  std::cout << "Write Misses:          " << write_misses << std::endl;
  std::cout << name << " ";
  std::cout << "Writebacks:            " << writebacks << std::endl;
  std::cout << name << " ";
  std::cout << "Miss Rate:             " << mr << '%' << std::endl;
}

uint64_t* cache_sim_t::check_tag(uint64_t addr)
{
  size_t idx = (addr >> idx_shift) & (sets-1); // Extract index from addr
  size_t tag = (addr >> idx_shift) | VALID; // Extract tag from addr, set valid = true

  for (size_t i = 0; i < ways; i++)
    if (tag == (tags[idx*ways + i] & ~DIRTY)) // If tag matches an entry in the cache...
      return &tags[idx*ways + i]; // Return the address in the cache where the match occurs

  return NULL;
}

uint64_t cache_sim_t::victimize(uint64_t addr)
{
  size_t idx = (addr >> idx_shift) & (sets-1); // Extract index from addr
  size_t way = lfsr.next() % ways; // Get way for this addr
  uint64_t victim = tags[idx*ways + way]; // Set victim to be old value in cache
  tags[idx*ways + way] = (addr >> idx_shift) | VALID; // Set cache here to be new addr
  return victim;
}

//Modify this
void cache_sim_t::access(uint64_t addr, size_t bytes, bool store)
{
  store ? write_accesses++ : read_accesses++; // Increment write or read accesses based on instr
  (store ? bytes_written : bytes_read) += bytes; // Increment # bytes read or written depending

  uint64_t* hit_way = check_tag(addr); // Set hit_way to point to a potential matched address
  if (likely(hit_way != NULL)) // CACHE HIT
  {
    if (store) // If the instruction is a write...
      *hit_way |= DIRTY; // Set the value of this block to dirty because this was a write
    return;
  }
  for (int i = 0; i < 3; i++) { // Search victim cache...
      if (victim_cache[i] == (((addr >> idx_shift) | VALID) & ~DIRTY) && ~store) { // VC HIT!
          return;
      }
  } // If didn't return here, we have a miss

  store ? write_misses++ : read_misses++; // Increment one of the miss counts
    
  uint64_t victim = victimize(addr);  // Replace our victim and save it here
    
  if ((victim & VALID) == VALID) { // If victim is valid...
      //int rand_index = rand() % 3; // Generate random index to be replaced in victim cache
      victim_cache[0] = victim; // Add victim to victim cache (assuming no vc hit yet)
  }

  if ((victim & (VALID | DIRTY)) == (VALID | DIRTY)) // If victim is valid and dirty...
  {
    uint64_t dirty_addr = (victim & ~(VALID | DIRTY)) << idx_shift;
    if (miss_handler)
      miss_handler->access(dirty_addr, linesz, true); // Write back victimized data to memory
    writebacks++;
  }

  if (miss_handler)
    miss_handler->access(addr & ~(linesz-1), linesz, false);

  if (store)
    *check_tag(addr) |= DIRTY; // Set this block to dirty because this was a write
}

fa_cache_sim_t::fa_cache_sim_t(size_t ways, size_t linesz, const char* name)
  : cache_sim_t(1, ways, linesz, name)
{
}

uint64_t* fa_cache_sim_t::check_tag(uint64_t addr)
{
  auto it = tags.find(addr >> idx_shift); // Search cache for tag
  return it == tags.end() ? NULL : &it->second; // Return
}

uint64_t fa_cache_sim_t::victimize(uint64_t addr)
{
  uint64_t old_tag = 0;
  if (tags.size() == ways)
  {
    auto it = tags.begin();
    std::advance(it, lfsr.next() % ways);
    old_tag = it->second;
    tags.erase(it);
  }
  tags[addr >> idx_shift] = (addr >> idx_shift) | VALID;
  return old_tag;
}
