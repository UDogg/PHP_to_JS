<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    public function up(): void
    {
        Schema::create('marquee', function (Blueprint $table) {
            $table->id();
            $table->string("usertype");
            $table->string('status')->default('N');
            $table->timestamps();
        });
    }
    
    public function down(): void
    {
        Schema::dropIfExists('marquee');
    }
};
