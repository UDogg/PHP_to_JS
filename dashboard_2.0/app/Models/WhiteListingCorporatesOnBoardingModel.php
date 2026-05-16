<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class WhiteListingCorporatesOnBoardingModel extends Model
{
    use HasFactory;
    protected $table = "white_listing_corporates_on_boarding_master";
    protected $fillable = [
        'id',
        'corporates_on_boarding_id',
        'email_id',
        'mobile_no',
        'status'
    ];
}
