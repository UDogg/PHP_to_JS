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
        //
        if(!Schema::hasTable('policy_status_filter_master')) {
            Schema::create('policy_status_filter_master', function (Blueprint $table) {
                $table->id();
                $table->string('filtername')->nullable();
                $table->string('type')->nullable();
                $table->string('key')->nullable();
                $table->string('value')->nullable();
                $table->integer('lob')->nullable();
                $table->integer('column')->nullable();
                $table->timestamps();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
        Schema::dropIfExists('policy_status_filter_master');
    }
};
