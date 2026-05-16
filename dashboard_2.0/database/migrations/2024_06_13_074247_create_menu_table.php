<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        if (!Schema::hasTable('menu')){
            Schema::create('menu', function (Blueprint $table) {
                $table->increments('menu_id');
                $table->string('menu_name',50);
                $table->string('menu_link',128);
                $table->string('menu_slug',50);
                $table->timestamps();
                $table->softDeletes();
            });
        }
        
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('menu');
    }
};
