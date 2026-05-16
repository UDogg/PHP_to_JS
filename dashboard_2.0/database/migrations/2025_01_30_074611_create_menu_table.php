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
        if (!Schema::hasTable('menu')) {

            Schema::table('menu', function (Blueprint $table) {
                $table->id('menu_id')->nullable();
                $table->string('menu_name')->nullable();
                $table->string('menu_link')->nullable();
                $table->string('menu_slug')->nullable();
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
