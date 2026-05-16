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
        if(!Schema::hasTable('ui_customizations')) {

            Schema::create('ui_customizations', function (Blueprint $table) {
                $table->id('placeholder_id');
                $table->string('username');
                $table->string('password');
                $table->string('broker_name');
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
        Schema::dropIfExists('placeholder_id');
    }
};
