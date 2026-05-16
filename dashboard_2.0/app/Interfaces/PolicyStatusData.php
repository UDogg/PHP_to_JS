<?php

namespace App\Interfaces;

interface PolicyStatusData
{
    //To Get The Data From The MongoDB
    public function fetchdata($isRenewal);
  
}