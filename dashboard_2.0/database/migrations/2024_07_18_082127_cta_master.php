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
        if(!Schema::hasTable('cta_master')) {

            Schema::create('cta_master', function (Blueprint $table) {
                $table->id('id');
                $table->string('stage');
                $table->string('cta_name');
                $table->string('redirection_url');
                $table->string('lob');
                $table->timestamps();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('cta_master');

    }
};
