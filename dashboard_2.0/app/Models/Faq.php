<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Database\Eloquent\SoftDeletes;

class Faq extends Model
{
    use HasFactory,SoftDeletes;

    protected  $table = 'faqs';
    protected  $primaryKey = 'faq_id';
    protected  $fillable = [
        'tag',
        'question',
        'answer',

    ];
        public function tagName()
    {
        return $this->belongsTo(TagName::class, 'tag', 'tag_id');
    }


}
